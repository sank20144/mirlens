use std::collections::{HashMap, HashSet};

use rustc_hir::def_id::DefId;
use rustc_middle::mir;
use rustc_middle::ty::{self, TyCtxt};

use crate::walk::{self, Visitor};

#[derive(Clone, PartialEq)]
enum Sym {
    Input(String),
    Const(i128),
    Bin(String, Box<Sym>, Box<Sym>),
    Un(String, Box<Sym>),
    Cond(Box<Sym>, Box<Sym>, Box<Sym>),
    Ref { target: usize, name: String },
    Call(String, Vec<Sym>),
    Field(Box<Sym>, String),
    Aggregate(Vec<Sym>),
    Index(Box<Sym>, Box<Sym>),
    Unknown,
}

impl std::fmt::Display for Sym {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Sym::Input(name) => write!(f, "{name}"),
            Sym::Const(v) => write!(f, "{v}"),
            Sym::Bin(op, l, r) => write!(f, "({l} {op} {r})"),
            Sym::Un(op, v) => write!(f, "{op}{v}"),
            Sym::Cond(c, t, e) => write!(f, "(if {c} {{ {t} }} else {{ {e} }})"),
            Sym::Ref { name, .. } => write!(f, "&{name}"),
            Sym::Call(name, args) => {
                let args: Vec<String> = args.iter().map(|a| a.to_string()).collect();
                write!(f, "{name}({})", args.join(", "))
            }
            Sym::Field(base, name) => write!(f, "{base}.{name}"),
            Sym::Aggregate(elems) => {
                let parts: Vec<String> = elems.iter().map(|e| e.to_string()).collect();
                write!(f, "({})", parts.join(", "))
            }
            Sym::Index(base, idx) => write!(f, "{base}[{idx}]"),
            Sym::Unknown => write!(f, "?"),
        }
    }
}

fn single_deref(p: &mir::Place<'_>) -> bool {
    p.projection.len() == 1 && matches!(p.projection[0], mir::ProjectionElem::Deref)
}

struct Summary<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    names: Vec<String>,
    tys: Vec<ty::Ty<'tcx>>,
    env: Vec<Sym>,
    summaries: &'a HashMap<DefId, FnSummary>,
    approx_call: bool,
}

impl<'a, 'tcx> Visitor<'tcx> for Summary<'a, 'tcx> {
    fn statement(&mut self, stmt: &mir::Statement<'tcx>) {
        if let mir::StatementKind::Assign(b) = &stmt.kind {
            let (place, rv) = &**b;
            let v = self.rvalue(rv);
            let dest = place.local.as_usize();
            if place.projection.is_empty() {
                self.env[dest] = v;
            } else if single_deref(place) {
                let target = match &self.env[dest] {
                    Sym::Ref { target, .. } => Some(*target),
                    _ => None,
                };
                if let Some(t) = target {
                    self.env[t] = v;
                }
            }
        }
    }

    fn terminator(&mut self, term: &mir::Terminator<'tcx>) {
        if let mir::TerminatorKind::Call { func, args, destination, .. } = &term.kind {
            if destination.projection.is_empty() {
                let dest = destination.local.as_usize();
                let actuals: Vec<Sym> = args.iter().map(|a| self.operand(&a.node)).collect();
                self.env[dest] = self.call_value(func, actuals);
            }
        }
    }
}

impl<'a, 'tcx> Summary<'a, 'tcx> {
    fn call_value(&mut self, func: &mir::Operand<'tcx>, actuals: Vec<Sym>) -> Sym {
        let Some(callee) = callee_def_id(func).and_then(|d| self.summaries.get(&d)) else {
            return match self.callee_name(func) {
                Some(name) => Sym::Call(name, actuals),
                None => Sym::Unknown,
            };
        };
        let (cparams, cret, cwrites, approx) =
            (callee.params.clone(), callee.ret.clone(), callee.writes.clone(), callee.note.is_some());
        if approx {
            self.approx_call = true;
        }
        let binding: HashMap<&str, &Sym> = cparams.iter().map(String::as_str).zip(&actuals).collect();
        for (param, w) in &cwrites {
            if let Some(Sym::Ref { target, .. }) = actuals.get(*param) {
                self.env[*target] = simplify(substitute(w, &binding));
            }
        }
        simplify(substitute(&cret, &binding))
    }

    fn rvalue(&self, rv: &mir::Rvalue<'tcx>) -> Sym {
        match rv {
            mir::Rvalue::Use(op, _) => self.operand(op),
            mir::Rvalue::BinaryOp(op, b) => {
                let (l, r) = &**b;
                mk_bin(op, self.operand(l), self.operand(r))
            }
            mir::Rvalue::UnaryOp(op, operand) => mk_un(op, self.operand(operand)),
            mir::Rvalue::Cast(_, operand, _) => self.operand(operand),
            mir::Rvalue::Ref(_, _, place) | mir::Rvalue::RawPtr(_, place) => self.make_ref(place),
            mir::Rvalue::Aggregate(_, operands) => {
                Sym::Aggregate(operands.iter().map(|o| self.operand(o)).collect())
            }
            _ => Sym::Unknown,
        }
    }

    fn callee_name(&self, func: &mir::Operand<'tcx>) -> Option<String> {
        let c = match func {
            mir::Operand::Constant(c) => c,
            _ => return None,
        };
        match c.const_.ty().kind() {
            ty::FnDef(def_id, _) => Some(self.tcx.item_name(*def_id).to_string()),
            _ => None,
        }
    }

    fn make_ref(&self, place: &mir::Place<'tcx>) -> Sym {
        if place.projection.is_empty() {
            let target = place.local.as_usize();
            Sym::Ref { target, name: self.names[target].clone() }
        } else if single_deref(place) {
            match &self.env[place.local.as_usize()] {
                Sym::Ref { target, name } => Sym::Ref { target: *target, name: name.clone() },
                _ => Sym::Unknown,
            }
        } else {
            Sym::Unknown
        }
    }

    fn operand(&self, op: &mir::Operand<'tcx>) -> Sym {
        match op {
            mir::Operand::Copy(p) | mir::Operand::Move(p) => self.place_value(p),
            mir::Operand::Constant(c) => match c.const_.try_eval_bits(self.tcx, self.typing_env) {
                Some(bits) => Sym::Const(bits as i128),
                None => Sym::Unknown,
            },
            _ => Sym::Unknown,
        }
    }

    fn place_value(&self, p: &mir::Place<'tcx>) -> Sym {
        let local = p.local.as_usize();
        if p.projection.is_empty() {
            self.env[local].clone()
        } else if single_deref(p) {
            match &self.env[local] {
                Sym::Ref { target, .. } => self.env[*target].clone(),
                _ => Sym::Unknown,
            }
        } else if let [mir::ProjectionElem::Field(idx, _)] = &p.projection[..] {
            let i = idx.as_usize();
            match self.env[local].clone() {
                Sym::Aggregate(elems) => elems.into_iter().nth(i).unwrap_or(Sym::Unknown),
                Sym::Unknown => Sym::Unknown,
                base => Sym::Field(Box::new(base), self.field_name(self.tys[local], i)),
            }
        } else if let [mir::ProjectionElem::Index(li)] = &p.projection[..] {
            index_into(self.env[local].clone(), self.env[li.as_usize()].clone())
        } else if let [mir::ProjectionElem::ConstantIndex { offset, from_end: false, .. }] =
            &p.projection[..]
        {
            index_into(self.env[local].clone(), Sym::Const(*offset as i128))
        } else {
            Sym::Unknown
        }
    }

    fn field_name(&self, base_ty: ty::Ty<'tcx>, idx: usize) -> String {
        if let ty::Adt(def, _) = base_ty.kind() {
            if def.is_struct() {
                if let Some(fd) = def.non_enum_variant().fields.iter().nth(idx) {
                    return fd.name.to_string();
                }
            }
        }
        idx.to_string()
    }
}

fn index_into(base: Sym, idx: Sym) -> Sym {
    if let (Sym::Aggregate(elems), Sym::Const(i)) = (&base, &idx) {
        if let Ok(i) = usize::try_from(*i) {
            if let Some(e) = elems.get(i) {
                return e.clone();
            }
        }
    }
    match base {
        Sym::Unknown => Sym::Unknown,
        base => Sym::Index(Box::new(base), Box::new(idx)),
    }
}

fn mk_bin(op: &mir::BinOp, l: Sym, r: Sym) -> Sym {
    mk_bin_sym(bin_op(op), l, r)
}

fn mk_un(op: &mir::UnOp, v: Sym) -> Sym {
    mk_un_sym(un_op(op), v)
}

fn mk_bin_sym(op: String, l: Sym, r: Sym) -> Sym {
    if let (Sym::Const(a), Sym::Const(b)) = (&l, &r) {
        if let Some(v) = fold_sym(&op, *a, *b) {
            return Sym::Const(v);
        }
    }
    Sym::Bin(op, Box::new(l), Box::new(r))
}

fn mk_un_sym(op: String, v: Sym) -> Sym {
    if op == "-" {
        if let Sym::Const(a) = &v {
            if let Some(n) = a.checked_neg() {
                return Sym::Const(n);
            }
        }
    }
    Sym::Un(op, Box::new(v))
}

fn fold_sym(op: &str, a: i128, b: i128) -> Option<i128> {
    let shift = |amt: i128| (0..128).contains(&amt).then_some(amt as u32);
    match op {
        "+" => a.checked_add(b),
        "-" => a.checked_sub(b),
        "*" => a.checked_mul(b),
        "/" => a.checked_div(b),
        "%" => a.checked_rem(b),
        "^" => Some(a ^ b),
        "&" => Some(a & b),
        "|" => Some(a | b),
        "<<" => shift(b).and_then(|s| a.checked_shl(s)),
        ">>" => shift(b).and_then(|s| a.checked_shr(s)),
        "==" => Some((a == b) as i128),
        "!=" => Some((a != b) as i128),
        "<" => Some((a < b) as i128),
        "<=" => Some((a <= b) as i128),
        ">" => Some((a > b) as i128),
        ">=" => Some((a >= b) as i128),
        _ => None,
    }
}

fn bin_op(op: &mir::BinOp) -> String {
    use mir::BinOp::*;
    match op {
        Add | AddUnchecked | AddWithOverflow => "+",
        Sub | SubUnchecked | SubWithOverflow => "-",
        Mul | MulUnchecked | MulWithOverflow => "*",
        Div => "/",
        Rem => "%",
        BitXor => "^",
        BitAnd => "&",
        BitOr => "|",
        Shl | ShlUnchecked => "<<",
        Shr | ShrUnchecked => ">>",
        Eq => "==",
        Ne => "!=",
        Lt => "<",
        Le => "<=",
        Gt => ">",
        Ge => ">=",
        other => return format!("{other:?}"),
    }
    .into()
}

fn un_op(op: &mir::UnOp) -> String {
    match op {
        mir::UnOp::Neg => "-".into(),
        mir::UnOp::Not => "!".into(),
        other => format!("{other:?}"),
    }
}

pub(crate) fn local_names(body: &mir::Body<'_>) -> Vec<String> {
    let mut names: Vec<String> = (0..body.local_decls.len()).map(|i| format!("_{i}")).collect();
    for info in &body.var_debug_info {
        if let mir::VarDebugInfoContents::Place(p) = &info.value {
            if p.projection.is_empty() {
                names[p.local.as_usize()] = info.name.as_str().to_string();
            }
        }
    }
    names
}

#[derive(Clone)]
enum Guard {
    Eq(Sym, i128),
    Otherwise(Sym),
}

pub struct FnSummary {
    params: Vec<String>,
    ret: Sym,
    writes: Vec<(usize, Sym)>,
    note: Option<&'static str>,
}

impl std::fmt::Display for FnSummary {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut parts: Vec<String> =
            self.writes.iter().map(|(p, w)| format!("writes *{} = {}", self.params[*p], w)).collect();
        parts.push(format!("returns {}", self.ret));
        write!(f, "{}", parts.join("; "))?;
        if let Some(note) = self.note {
            write!(f, "  ({note})")?;
        }
        Ok(())
    }
}

pub fn summarize_crate<'tcx>(
    tcx: TyCtxt<'tcx>,
    funcs: &[(DefId, &mir::Body<'tcx>)],
) -> HashMap<DefId, FnSummary> {
    let in_crate: HashSet<DefId> = funcs.iter().map(|(d, _)| *d).collect();
    let bodies: HashMap<DefId, &mir::Body<'tcx>> = funcs.iter().map(|(d, b)| (*d, *b)).collect();

    let mut graph: HashMap<DefId, Vec<DefId>> = HashMap::new();
    for (d, body) in funcs {
        graph.insert(*d, direct_callees(body, &in_crate));
    }

    let mut summaries = HashMap::new();
    for d in call_order(funcs, &graph) {
        let (fs, _) = summarize_fn(tcx, bodies[&d], &summaries);
        summaries.insert(d, fs);
    }
    summaries
}

pub fn emit_dot<'tcx>(
    tcx: TyCtxt<'tcx>,
    funcs: &[(DefId, &mir::Body<'tcx>)],
    summaries: &HashMap<DefId, FnSummary>,
) {
    let in_crate: HashSet<DefId> = funcs.iter().map(|(d, _)| *d).collect();
    let node: HashMap<DefId, usize> = funcs.iter().enumerate().map(|(i, (d, _))| (*d, i)).collect();

    println!("digraph calls {{");
    println!("  node [shape=box, fontname=monospace];");
    for (i, (d, _)) in funcs.iter().enumerate() {
        let fs = &summaries[d];
        let head = escape(&format!("{}({})", tcx.def_path_str(*d), fs.params.join(", ")));
        let summary = escape(&fs.to_string());
        let style = if fs.note.is_some() { ", style=dashed" } else { "" };
        println!("  n{i} [label=\"{head}\\n{summary}\"{style}];");
    }
    for (i, (_, body)) in funcs.iter().enumerate() {
        for callee in direct_callees(body, &in_crate) {
            println!("  n{i} -> n{};", node[&callee]);
        }
    }
    println!("}}");
}

fn escape(s: &str) -> String {
    s.replace('\\', "\\\\").replace('"', "\\\"")
}

fn summarize_fn<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &mir::Body<'tcx>,
    summaries: &HashMap<DefId, FnSummary>,
) -> (FnSummary, Vec<Sym>) {
    let arg_count = body.arg_count;
    let names0 = local_names(body);
    let params: Vec<String> = (1..=arg_count).map(|i| names0[i].clone()).collect();
    let tys0: Vec<ty::Ty<'tcx>> = body.local_decls.iter().map(|d| d.ty).collect();

    let mut names = names0.clone();
    let mut tys = tys0.clone();
    let mut init = vec![Sym::Unknown; body.local_decls.len()];
    let mut pointee_of = vec![None; arg_count + 1];
    for i in 1..=arg_count {
        if matches!(tys0[i].kind(), ty::Ref(..) | ty::RawPtr(..)) {
            let slot = init.len();
            init.push(Sym::Input(format!("*{}", names0[i])));
            names.push(format!("*{}", names0[i]));
            tys.push(tys0[i]);
            init[i] = Sym::Ref { target: slot, name: names0[i].clone() };
            pointee_of[i] = Some(slot);
        } else {
            init[i] = Sym::Input(names0[i].clone());
        }
    }

    let mut s = Summary {
        tcx,
        typing_env: ty::TypingEnv::fully_monomorphized(),
        names,
        tys,
        env: init.clone(),
        summaries,
        approx_call: false,
    };

    let (env, note) = match topo_order(body) {
        Some(order) => {
            let (env, imprecise) = s.eval_cfg(body, &order, init);
            (env, (imprecise || s.approx_call).then_some("approximate"))
        }
        None => {
            s.env = init;
            walk::walk(body, &mut s);
            (s.env.clone(), Some("approximate: loops not modelled"))
        }
    };

    let mut writes = Vec::new();
    for i in 1..=arg_count {
        if let Some(slot) = pointee_of[i] {
            let v = simplify(env[slot].clone());
            if v != Sym::Input(format!("*{}", params[i - 1])) {
                writes.push((i - 1, v));
            }
        }
    }
    let ret = simplify(env[0].clone());
    (FnSummary { params, ret, writes, note }, env)
}

pub fn local_values<'tcx>(tcx: TyCtxt<'tcx>, funcs: &[(DefId, &mir::Body<'tcx>)]) -> HashMap<DefId, Vec<String>> {
    let summaries = summarize_crate(tcx, funcs);
    funcs
        .iter()
        .map(|(d, body)| {
            let (_, env) = summarize_fn(tcx, body, &summaries);
            let values = (0..body.local_decls.len()).map(|i| simplify(env[i].clone()).to_string()).collect();
            (*d, values)
        })
        .collect()
}

pub(crate) fn callee_def_id(func: &mir::Operand<'_>) -> Option<DefId> {
    if let mir::Operand::Constant(c) = func {
        if let ty::FnDef(def_id, _) = c.const_.ty().kind() {
            return Some(*def_id);
        }
    }
    None
}

pub(crate) fn direct_callees(body: &mir::Body<'_>, in_crate: &HashSet<DefId>) -> Vec<DefId> {
    let mut out = Vec::new();
    for bb in body.basic_blocks.iter() {
        if let mir::TerminatorKind::Call { func, .. } = &bb.terminator().kind {
            if let Some(did) = callee_def_id(func) {
                if in_crate.contains(&did) && !out.contains(&did) {
                    out.push(did);
                }
            }
        }
    }
    out
}

pub(crate) fn call_order(funcs: &[(DefId, &mir::Body<'_>)], graph: &HashMap<DefId, Vec<DefId>>) -> Vec<DefId> {
    fn visit(d: DefId, graph: &HashMap<DefId, Vec<DefId>>, seen: &mut HashSet<DefId>, order: &mut Vec<DefId>) {
        if !seen.insert(d) {
            return;
        }
        for &callee in &graph[&d] {
            visit(callee, graph, seen, order);
        }
        order.push(d);
    }
    let mut seen = HashSet::new();
    let mut order = Vec::new();
    for (d, _) in funcs {
        visit(*d, graph, &mut seen, &mut order);
    }
    order
}

fn substitute(s: &Sym, binding: &HashMap<&str, &Sym>) -> Sym {
    let sub = |x: &Sym| Box::new(substitute(x, binding));
    match s {
        Sym::Input(name) => binding.get(name.as_str()).map_or_else(|| s.clone(), |v| (*v).clone()),
        Sym::Ref { .. } => Sym::Unknown,
        Sym::Const(_) | Sym::Unknown => s.clone(),
        Sym::Bin(op, l, r) => Sym::Bin(op.clone(), sub(l), sub(r)),
        Sym::Un(op, v) => Sym::Un(op.clone(), sub(v)),
        Sym::Cond(c, t, e) => Sym::Cond(sub(c), sub(t), sub(e)),
        Sym::Call(name, args) => Sym::Call(name.clone(), args.iter().map(|a| substitute(a, binding)).collect()),
        Sym::Field(base, name) => Sym::Field(sub(base), name.clone()),
        Sym::Aggregate(elems) => Sym::Aggregate(elems.iter().map(|e| substitute(e, binding)).collect()),
        Sym::Index(base, idx) => Sym::Index(sub(base), sub(idx)),
    }
}

fn simplify(s: Sym) -> Sym {
    match s {
        Sym::Bin(op, l, r) => mk_bin_sym(op, simplify(*l), simplify(*r)),
        Sym::Un(op, v) => mk_un_sym(op, simplify(*v)),
        Sym::Cond(c, t, e) => match simplify(*c) {
            Sym::Const(0) => simplify(*e),
            Sym::Const(_) => simplify(*t),
            c => Sym::Cond(Box::new(c), Box::new(simplify(*t)), Box::new(simplify(*e))),
        },
        Sym::Index(base, idx) => index_into(simplify(*base), simplify(*idx)),
        Sym::Field(base, name) => Sym::Field(Box::new(simplify(*base)), name),
        Sym::Aggregate(elems) => Sym::Aggregate(elems.into_iter().map(simplify).collect()),
        Sym::Call(name, args) => Sym::Call(name, args.into_iter().map(simplify).collect()),
        other => other,
    }
}

impl<'a, 'tcx> Summary<'a, 'tcx> {
    fn eval_cfg(&mut self, body: &mir::Body<'tcx>, order: &[mir::BasicBlock], init: Vec<Sym>) -> (Vec<Sym>, bool) {
        let preds = body.basic_blocks.predecessors();
        let n = body.basic_blocks.len();
        let mut exit: Vec<Option<Vec<Sym>>> = vec![None; n];
        let mut guard: Vec<Option<Guard>> = vec![None; n];
        let mut imprecise = false;
        let mut returns: Vec<Vec<Sym>> = Vec::new();

        for &bb in order {
            let ps = &preds[bb];
            let entry = if ps.is_empty() {
                init.clone()
            } else if ps.len() == 1 {
                exit[ps[0].as_usize()].clone().unwrap_or_else(|| init.clone())
            } else {
                let (merged, imp) = merge(ps, &exit, &guard);
                imprecise |= imp;
                merged
            };

            self.env = entry;
            let data = &body.basic_blocks[bb];
            for stmt in &data.statements {
                self.statement(stmt);
            }
            let term = data.terminator();
            self.terminator(term);
            exit[bb.as_usize()] = Some(self.env.clone());

            match &term.kind {
                mir::TerminatorKind::SwitchInt { discr, targets } => {
                    let d = self.operand(discr);
                    for (v, t) in targets.iter() {
                        guard[t.as_usize()] = Some(Guard::Eq(d.clone(), v as i128));
                    }
                    guard[targets.otherwise().as_usize()] = Some(Guard::Otherwise(d));
                }
                mir::TerminatorKind::Return => returns.push(self.env.clone()),
                _ => {
                    for succ in term.successors() {
                        if preds[succ].len() == 1 {
                            guard[succ.as_usize()] = guard[bb.as_usize()].clone();
                        }
                    }
                }
            }
        }

        match returns.as_slice() {
            [only] => (only.clone(), imprecise),
            [first, rest @ ..] if rest.iter().all(|e| e[0] == first[0]) => (first.clone(), imprecise),
            _ => (vec![Sym::Unknown; init.len()], true),
        }
    }
}

fn merge(preds: &[mir::BasicBlock], exit: &[Option<Vec<Sym>>], guard: &[Option<Guard>]) -> (Vec<Sym>, bool) {
    let avail: Vec<mir::BasicBlock> =
        preds.iter().copied().filter(|p| exit[p.as_usize()].is_some()).collect();
    let env = |p: mir::BasicBlock| exit[p.as_usize()].as_ref().unwrap();
    let mut out = Vec::new();
    let mut imprecise = false;
    for i in 0..env(avail[0]).len() {
        let first = &env(avail[0])[i];
        if avail.iter().all(|p| env(*p)[i] == *first) {
            out.push(first.clone());
        } else if let [a, b] = avail[..] {
            match branch_value(&env(a)[i], guard[a.as_usize()].as_ref(), &env(b)[i], guard[b.as_usize()].as_ref()) {
                Some(v) => out.push(v),
                None => {
                    out.push(Sym::Unknown);
                    imprecise = true;
                }
            }
        } else {
            out.push(Sym::Unknown);
            imprecise = true;
        }
    }
    (out, imprecise)
}

fn branch_value(va: &Sym, ga: Option<&Guard>, vb: &Sym, gb: Option<&Guard>) -> Option<Sym> {
    let (d, val, eq_val, oth_val) = match (ga?, gb?) {
        (Guard::Eq(d1, v), Guard::Otherwise(d2)) if d1 == d2 => (d1, *v, va, vb),
        (Guard::Otherwise(d2), Guard::Eq(d1, v)) if d1 == d2 => (d1, *v, vb, va),
        _ => return None,
    };
    if val == 0 {
        Some(Sym::Cond(Box::new(d.clone()), Box::new(oth_val.clone()), Box::new(eq_val.clone())))
    } else {
        let cond = Sym::Bin("==".into(), Box::new(d.clone()), Box::new(Sym::Const(val)));
        Some(Sym::Cond(Box::new(cond), Box::new(eq_val.clone()), Box::new(oth_val.clone())))
    }
}

pub(crate) fn has_loop(body: &mir::Body<'_>) -> bool {
    topo_order(body).is_none()
}

fn topo_order(body: &mir::Body<'_>) -> Option<Vec<mir::BasicBlock>> {
    #[derive(Clone, Copy, PartialEq)]
    enum Mark {
        Open,
        Done,
    }
    let succs: Vec<Vec<mir::BasicBlock>> =
        body.basic_blocks.iter().map(|d| d.terminator().successors().collect()).collect();
    let mut mark: Vec<Option<Mark>> = vec![None; succs.len()];
    let mut post = Vec::new();
    let mut stack = vec![(mir::START_BLOCK, 0usize)];
    mark[mir::START_BLOCK.as_usize()] = Some(Mark::Open);
    while let Some(&mut (bb, ref mut i)) = stack.last_mut() {
        let edges = &succs[bb.as_usize()];
        if *i < edges.len() {
            let s = edges[*i];
            *i += 1;
            match mark[s.as_usize()] {
                None => {
                    mark[s.as_usize()] = Some(Mark::Open);
                    stack.push((s, 0));
                }
                Some(Mark::Open) => return None,
                Some(Mark::Done) => {}
            }
        } else {
            mark[bb.as_usize()] = Some(Mark::Done);
            post.push(bb);
            stack.pop();
        }
    }
    post.reverse();
    Some(post)
}

use rustc_hir::def_id::DefId;
use rustc_middle::mir;
use rustc_middle::ty::{self, TyCtxt};

use crate::summary;

type Addr = usize;
type Step = usize;

#[derive(Clone, Copy)]
struct Lifetime {
    id: usize,
    start: Step,
    end: Step,
}

impl Lifetime {
    fn active(&self, step: Step) -> bool {
        self.start <= step && step < self.end
    }
    fn contains(&self, inner: &Lifetime) -> bool {
        self.start <= inner.start && inner.end <= self.end
    }
}

#[derive(Clone, Copy)]
enum Ownership {
    Owned(Addr, Lifetime),
    MutOwned(Addr, Lifetime),
    SharedRef(Addr, Lifetime),
    MutRef(Addr, Lifetime),
}

impl Ownership {
    fn addr(&self) -> Addr {
        match self {
            Ownership::Owned(a, _) | Ownership::MutOwned(a, _) | Ownership::SharedRef(a, _) | Ownership::MutRef(a, _) => *a,
        }
    }
    fn lifetime(&self) -> Lifetime {
        match self {
            Ownership::Owned(_, l) | Ownership::MutOwned(_, l) | Ownership::SharedRef(_, l) | Ownership::MutRef(_, l) => *l,
        }
    }
    fn kind(&self) -> &'static str {
        match self {
            Ownership::Owned(..) => "Owned",
            Ownership::MutOwned(..) => "MutOwned",
            Ownership::SharedRef(..) => "SharedRef",
            Ownership::MutRef(..) => "MutRef",
        }
    }
}

#[derive(Clone)]
enum LocState {
    Owned,
    Shared(Vec<Lifetime>),
    Mut(Vec<Lifetime>),
}

impl LocState {
    fn label(&self) -> String {
        let ids = |lts: &[Lifetime]| lts.iter().map(|l| format!("lt{}", l.id)).collect::<Vec<_>>().join(", ");
        match self {
            LocState::Owned => "LocOwned".into(),
            LocState::Shared(lts) => format!("LocShared[{}]", ids(lts)),
            LocState::Mut(lts) => format!("LocMut[{}]", ids(lts)),
        }
    }
}

#[derive(Clone)]
enum Val {
    Int(i128),
    Bool(bool),
    Unit,
    Unknown,
    Param(usize),
    In(usize),
}

impl std::fmt::Display for Val {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Val::Int(v) => write!(f, "{v}"),
            Val::Bool(b) => write!(f, "{b}"),
            Val::Unit => write!(f, "()"),
            Val::Unknown => write!(f, "?"),
            Val::Param(n) => write!(f, "arg{n}"),
            Val::In(n) => write!(f, "*arg{n}"),
        }
    }
}

#[derive(Clone)]
struct Cell {
    value: Val,
    state: LocState,
    owner: Lifetime,
}

#[derive(Clone)]
struct State<'tcx> {
    tcx: TyCtxt<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    names: Vec<String>,
    muts: Vec<bool>,
    refs: Vec<bool>,
    arg_count: usize,
    lifetimes: Vec<Lifetime>,
    block_step: Vec<Step>,
    heap: Vec<Cell>,
    vars: Vec<Option<Ownership>>,
    step: Step,
    ub: Vec<String>,
}

#[derive(Clone)]
enum Ret {
    Val(Val),
    Ref(usize),
}

pub struct HeapSummary {
    writes: Vec<(usize, Val)>,
    ret: Ret,
}

impl<'tcx> State<'tcx> {
    fn expire(&mut self, a: Addr) {
        let step = self.step;
        let keep = |lts: &Vec<Lifetime>| lts.iter().copied().filter(|l| l.active(step)).collect::<Vec<_>>();
        let cell = &mut self.heap[a];
        cell.state = match &cell.state {
            LocState::Owned => LocState::Owned,
            LocState::Shared(lts) => match keep(lts) {
                live if live.is_empty() => LocState::Owned,
                live => LocState::Shared(live),
            },
            LocState::Mut(lts) => match keep(lts) {
                live if live.is_empty() => LocState::Owned,
                live => LocState::Mut(live),
            },
        };
    }

    fn flag(&mut self, msg: String) {
        self.ub.push(msg);
    }

    fn ref_arg(&self, op: &mir::Operand<'_>) -> Option<usize> {
        match op {
            mir::Operand::Copy(p) | mir::Operand::Move(p) if p.projection.is_empty() => {
                let l = p.local.as_usize();
                matches!(self.vars[l], Some(Ownership::SharedRef(..)) | Some(Ownership::MutRef(..))).then_some(l)
            }
            _ => None,
        }
    }

    fn subst(&mut self, v: &Val, actuals: &[(Val, Option<usize>)]) -> Val {
        match v {
            Val::Param(i) => actuals.get(*i).map_or(Val::Unknown, |a| a.0.clone()),
            Val::In(i) => match actuals.get(*i).and_then(|a| a.1) {
                Some(rl) => self.read_through(rl),
                None => Val::Unknown,
            },
            other => other.clone(),
        }
    }

    fn instantiate(&mut self, summary: &HeapSummary, actuals: &[(Val, Option<usize>)], dest: usize) {
        for (param, wv) in &summary.writes {
            if let Some(rl) = actuals.get(*param).and_then(|a| a.1) {
                let v = self.subst(wv, actuals);
                self.write_through(rl, v);
            }
        }
        match &summary.ret {
            Ret::Val(v) => {
                let v = self.subst(v, actuals);
                self.assign_owned(dest, v);
            }
            Ret::Ref(i) => match actuals.get(*i).and_then(|a| a.1) {
                Some(rl) => self.alias_ref(dest, rl),
                None => self.assign_owned(dest, Val::Unknown),
            },
        }
    }

    fn fmt_val(&self, v: &Val) -> String {
        let name = |n: usize| self.names.get(n + 1).cloned().unwrap_or_else(|| format!("arg{n}"));
        match v {
            Val::Param(n) => name(*n),
            Val::In(n) => format!("*{}", name(*n)),
            other => other.to_string(),
        }
    }

    fn seed_params(&mut self, body: &mir::Body<'tcx>) {
        for i in 1..=self.arg_count {
            let lt = self.lifetimes[i];
            let a = self.heap.len();
            if self.refs[i] {
                let mutbl = match body.local_decls[mir::Local::from_usize(i)].ty.kind() {
                    ty::Ref(_, _, m) => m.is_mut(),
                    ty::RawPtr(_, m) => m.is_mut(),
                    _ => false,
                };
                let owner = Lifetime { id: 1000 + i, start: 0, end: usize::MAX };
                let state = if mutbl { LocState::Mut(vec![lt]) } else { LocState::Shared(vec![lt]) };
                self.heap.push(Cell { value: Val::In(i - 1), state, owner });
                self.vars[i] = Some(if mutbl { Ownership::MutRef(a, lt) } else { Ownership::SharedRef(a, lt) });
            } else {
                self.heap.push(Cell { value: Val::Param(i - 1), state: LocState::Owned, owner: lt });
                self.vars[i] = Some(if self.muts[i] { Ownership::MutOwned(a, lt) } else { Ownership::Owned(a, lt) });
            }
        }
    }

    fn assign_owned(&mut self, d: usize, val: Val) {
        if let Some(own) = self.vars[d] {
            let a = own.addr();
            self.expire(a);
            if !own.lifetime().active(self.step) {
                self.flag(format!("write to {} after its lifetime ended", self.names[d]));
                return;
            }
            if !self.muts[d] {
                self.flag(format!("write to immutable {}", self.names[d]));
                return;
            }
            match self.heap[a].state {
                LocState::Owned => self.heap[a].value = val,
                _ => self.flag(format!("write to {} while it is borrowed", self.names[d])),
            }
        } else {
            let a = self.heap.len();
            let lt = self.lifetimes[d];
            self.heap.push(Cell { value: val, state: LocState::Owned, owner: lt });
            self.vars[d] = Some(if self.muts[d] { Ownership::MutOwned(a, lt) } else { Ownership::Owned(a, lt) });
        }
    }

    fn reborrow(&mut self, d: usize, p: usize, mutable: bool) {
        let Some(own) = self.vars[p] else { return };
        let a = own.addr();
        let lt = self.lifetimes[d];
        self.expire(a);
        if mutable {
            match &mut self.heap[a].state {
                LocState::Mut(stack) => stack.insert(0, lt),
                LocState::Owned => self.heap[a].state = LocState::Mut(vec![lt]),
                LocState::Shared(_) => self.flag(format!("mutable reborrow through {} while shared-borrowed", self.names[p])),
            }
            self.vars[d] = Some(Ownership::MutRef(a, lt));
        } else {
            match &mut self.heap[a].state {
                LocState::Shared(lts) => lts.push(lt),
                LocState::Owned => self.heap[a].state = LocState::Shared(vec![lt]),
                LocState::Mut(stack) => stack.insert(0, lt),
            }
            self.vars[d] = Some(Ownership::SharedRef(a, lt));
        }
    }

    fn alias_ref(&mut self, d: usize, src: usize) {
        if let Some(own) = self.vars[src] {
            let a = own.addr();
            let lt = self.lifetimes[d];
            self.vars[d] = Some(match own {
                Ownership::MutRef(..) => Ownership::MutRef(a, lt),
                _ => Ownership::SharedRef(a, lt),
            });
        }
    }

    fn step_assign(&mut self, d: usize, rv: &mir::Rvalue<'tcx>) {
        match rv {
            mir::Rvalue::Ref(_, kind, t) if t.projection.is_empty() => {
                self.create_ref(d, t.local.as_usize(), matches!(kind, mir::BorrowKind::Mut { .. }));
            }
            mir::Rvalue::RawPtr(m, t) if t.projection.is_empty() => {
                self.create_ref(d, t.local.as_usize(), matches!(m, mir::RawPtrKind::Mut));
            }
            mir::Rvalue::Ref(_, kind, t) if single_deref(t) => {
                self.reborrow(d, t.local.as_usize(), matches!(kind, mir::BorrowKind::Mut { .. }));
            }
            mir::Rvalue::RawPtr(m, t) if single_deref(t) => {
                self.reborrow(d, t.local.as_usize(), matches!(m, mir::RawPtrKind::Mut));
            }
            mir::Rvalue::Use(op, _) | mir::Rvalue::Cast(_, op, _) if self.refs[d] => {
                match self.ref_source(op) {
                    Some(src) => self.alias_ref(d, src),
                    None => {
                        let v = self.eval(rv);
                        self.assign_owned(d, v);
                    }
                }
            }
            _ => {
                let v = self.eval(rv);
                self.assign_owned(d, v);
            }
        }
    }

    fn ref_source(&self, op: &mir::Operand<'_>) -> Option<usize> {
        let src = operand_locals(op)?;
        matches!(self.vars[src], Some(Ownership::SharedRef(..)) | Some(Ownership::MutRef(..))).then_some(src)
    }

    fn create_ref(&mut self, d: usize, t: usize, mutable: bool) {
        let Some(owner) = self.vars[t] else {
            self.flag(format!("borrow of {}, which owns nothing", self.names[t]));
            return;
        };
        let a = owner.addr();
        let borrow_lt = self.lifetimes[d];
        if !owner.lifetime().contains(&borrow_lt) {
            self.flag(format!("{} borrows {} for longer than it lives", self.names[d], self.names[t]));
            return;
        }
        self.expire(a);
        if mutable {
            match &self.heap[a].state {
                LocState::Owned => {
                    self.heap[a].state = LocState::Mut(vec![borrow_lt]);
                    self.vars[d] = Some(Ownership::MutRef(a, borrow_lt));
                }
                _ => self.flag(format!("mutable borrow of {} while it is already borrowed", self.names[t])),
            }
        } else {
            match &mut self.heap[a].state {
                LocState::Owned => {
                    self.heap[a].state = LocState::Shared(vec![borrow_lt]);
                    self.vars[d] = Some(Ownership::SharedRef(a, borrow_lt));
                }
                LocState::Shared(lts) => {
                    lts.push(borrow_lt);
                    self.vars[d] = Some(Ownership::SharedRef(a, borrow_lt));
                }
                LocState::Mut(_) => self.flag(format!("shared borrow of {} while mutably borrowed", self.names[t])),
            }
        }
    }

    fn write_through(&mut self, p: usize, val: Val) {
        let Some(own) = self.vars[p] else { return };
        let a = own.addr();
        self.expire(a);
        if !self.heap[a].owner.active(self.step) {
            self.flag(format!("write through {}, whose pointee has gone out of scope", self.names[p]));
            return;
        }
        match own {
            Ownership::MutRef(_, lt) if lt.active(self.step) => match &self.heap[a].state {
                LocState::Mut(stack) if matches!(stack.first(), Some(top) if top.id == lt.id) => {
                    self.heap[a].value = val;
                }
                _ => self.flag(format!("write through {}, which no longer holds the mutable borrow", self.names[p])),
            },
            Ownership::SharedRef(..) => self.flag(format!("write through shared reference {}", self.names[p])),
            _ => self.flag(format!("write through {} after its lifetime ended", self.names[p])),
        }
    }

    fn read_place(&mut self, place: &mir::Place<'_>) -> Val {
        let local = place.local.as_usize();
        if place.projection.is_empty() {
            self.read(local)
        } else if matches!(place.projection[..], [mir::ProjectionElem::Deref]) {
            self.read_through(local)
        } else {
            Val::Unknown
        }
    }

    fn read(&mut self, local: usize) -> Val {
        let Some(own) = self.vars[local] else { return Val::Unknown };
        let a = own.addr();
        self.expire(a);
        if !own.lifetime().active(self.step) {
            self.flag(format!("use of {} after its lifetime ended", self.names[local]));
            return Val::Unknown;
        }
        match &self.heap[a].state {
            LocState::Owned | LocState::Shared(_) => self.heap[a].value.clone(),
            LocState::Mut(_) => {
                self.flag(format!("read of {} while it is mutably borrowed", self.names[local]));
                Val::Unknown
            }
        }
    }

    fn read_through(&mut self, p: usize) -> Val {
        let Some(own) = self.vars[p] else { return Val::Unknown };
        let a = own.addr();
        self.expire(a);
        if !own.lifetime().active(self.step) {
            self.flag(format!("use of {} after its lifetime ended", self.names[p]));
            return Val::Unknown;
        }
        if !self.heap[a].owner.active(self.step) {
            self.flag(format!("dereference of {}, whose pointee has gone out of scope", self.names[p]));
            return Val::Unknown;
        }
        self.heap[a].value.clone()
    }

    fn eval(&mut self, rv: &mir::Rvalue<'tcx>) -> Val {
        match rv {
            mir::Rvalue::Use(op, _) => self.operand(op),
            mir::Rvalue::Cast(_, op, _) => self.operand(op),
            mir::Rvalue::UnaryOp(op, operand) => match (op, self.operand(operand)) {
                (mir::UnOp::Neg, Val::Int(a)) => a.checked_neg().map_or(Val::Unknown, Val::Int),
                (mir::UnOp::Not, Val::Bool(a)) => Val::Bool(!a),
                _ => Val::Unknown,
            },
            mir::Rvalue::BinaryOp(op, b) => {
                let (l, r) = &**b;
                match (self.operand(l), self.operand(r)) {
                    (Val::Int(a), Val::Int(c)) => fold(op, a, c),
                    _ => Val::Unknown,
                }
            }
            _ => Val::Unknown,
        }
    }

    fn operand(&mut self, op: &mir::Operand<'tcx>) -> Val {
        match op {
            mir::Operand::Copy(p) | mir::Operand::Move(p) => self.read_place(p),
            mir::Operand::Constant(c) => {
                let ty = c.const_.ty();
                match c.const_.try_eval_bits(self.tcx, self.typing_env) {
                    Some(bits) if ty.is_bool() => Val::Bool(bits != 0),
                    Some(bits) => Val::Int(bits as i128),
                    None if ty.is_unit() => Val::Unit,
                    None => Val::Unknown,
                }
            }
            _ => Val::Unknown,
        }
    }
}

fn fold(op: &mir::BinOp, a: i128, b: i128) -> Val {
    use mir::BinOp::*;
    let int = |o: Option<i128>| o.map_or(Val::Unknown, Val::Int);
    match op {
        Add | AddUnchecked => int(a.checked_add(b)),
        Sub | SubUnchecked => int(a.checked_sub(b)),
        Mul | MulUnchecked => int(a.checked_mul(b)),
        Div => int(a.checked_div(b)),
        Rem => int(a.checked_rem(b)),
        BitXor => Val::Int(a ^ b),
        BitAnd => Val::Int(a & b),
        BitOr => Val::Int(a | b),
        Eq => Val::Bool(a == b),
        Ne => Val::Bool(a != b),
        Lt => Val::Bool(a < b),
        Le => Val::Bool(a <= b),
        Gt => Val::Bool(a > b),
        Ge => Val::Bool(a >= b),
        _ => Val::Unknown,
    }
}

fn lifetimes(body: &mir::Body<'_>) -> Vec<Lifetime> {
    let n = body.local_decls.len();
    let mut first = vec![usize::MAX; n];
    let mut last = vec![0usize; n];
    let mut dead = vec![None; n];
    let mut step = 0;
    let mut mark = |local: usize, s: Step| {
        first[local] = first[local].min(s);
        last[local] = last[local].max(s);
    };
    for data in body.basic_blocks.iter() {
        for stmt in &data.statements {
            match &stmt.kind {
                mir::StatementKind::Assign(b) => {
                    let (place, rv) = &**b;
                    mark(place.local.as_usize(), step);
                    for local in rvalue_locals(rv) {
                        mark(local, step);
                    }
                }
                mir::StatementKind::StorageDead(l) => dead[l.as_usize()] = Some(step),
                _ => {}
            }
            step += 1;
        }
        for local in terminator_locals(data.terminator()) {
            mark(local, step);
        }
        step += 1;
    }
    (0..n)
        .map(|i| {
            let start = if first[i] == usize::MAX { 0 } else { first[i] };
            let ty = body.local_decls[mir::Local::from_usize(i)].ty;
            let is_ref = matches!(ty.kind(), ty::Ref(..) | ty::RawPtr(..));
            let end = if is_ref { last[i] + 1 } else { dead[i].map_or(last[i] + 1, |d| d + 1) };
            Lifetime { id: i, start, end }
        })
        .collect()
}

fn place_local(p: &mir::Place<'_>) -> usize {
    p.local.as_usize()
}

fn operand_locals(op: &mir::Operand<'_>) -> Option<usize> {
    match op {
        mir::Operand::Copy(p) | mir::Operand::Move(p) => Some(place_local(p)),
        _ => None,
    }
}

fn rvalue_locals(rv: &mir::Rvalue<'_>) -> Vec<usize> {
    match rv {
        mir::Rvalue::Use(op, _) | mir::Rvalue::Cast(_, op, _) | mir::Rvalue::UnaryOp(_, op) => {
            operand_locals(op).into_iter().collect()
        }
        mir::Rvalue::Ref(_, _, p) | mir::Rvalue::RawPtr(_, p) => vec![place_local(p)],
        mir::Rvalue::BinaryOp(_, b) => {
            let (l, r) = &**b;
            operand_locals(l).into_iter().chain(operand_locals(r)).collect()
        }
        _ => Vec::new(),
    }
}

fn terminator_locals(term: &mir::Terminator<'_>) -> Vec<usize> {
    let mut out = Vec::new();
    match &term.kind {
        mir::TerminatorKind::SwitchInt { discr, .. } => out.extend(operand_locals(discr)),
        mir::TerminatorKind::Call { func, args, destination, .. } => {
            out.extend(operand_locals(func));
            for a in args {
                out.extend(operand_locals(&a.node));
            }
            out.push(place_local(destination));
        }
        mir::TerminatorKind::Drop { place, .. } => out.push(place_local(place)),
        mir::TerminatorKind::Return => out.push(0),
        _ => {}
    }
    out
}

fn single_deref(p: &mir::Place<'_>) -> bool {
    matches!(p.projection[..], [mir::ProjectionElem::Deref])
}

pub fn analyze_crate<'tcx>(tcx: TyCtxt<'tcx>, funcs: &[(DefId, &mir::Body<'tcx>)]) {
    let sym = summary::local_values(tcx, funcs);
    let summaries = build_summaries(tcx, funcs);
    for (d, body) in funcs {
        let (paths, looped) = analyze_paths(tcx, body, &summaries);
        report_fn(tcx, *d, &paths, looped, sym.get(d));
    }
}

pub fn emit_dot<'tcx>(tcx: TyCtxt<'tcx>, funcs: &[(DefId, &mir::Body<'tcx>)]) {
    let in_crate: std::collections::HashSet<DefId> = funcs.iter().map(|(d, _)| *d).collect();
    let index: std::collections::HashMap<DefId, usize> =
        funcs.iter().enumerate().map(|(i, (d, _))| (*d, i)).collect();

    let sym = summary::local_values(tcx, funcs);
    let summaries = build_summaries(tcx, funcs);
    println!("digraph heap {{");
    println!("  compound=true;");
    println!("  node [shape=box, fontname=monospace];");
    for (i, (d, body)) in funcs.iter().enumerate() {
        let (paths, looped) = analyze_paths(tcx, body, &summaries);
        dot_fn(tcx, i, *d, &paths, looped, sym.get(d));
    }
    for (i, (_, body)) in funcs.iter().enumerate() {
        for callee in summary::direct_callees(body, &in_crate) {
            let j = index[&callee];
            println!("  h{i} -> h{j} [ltail=cluster_{i}, lhead=cluster_{j}];");
        }
    }
    println!("}}");
}

fn build_summaries<'tcx>(
    tcx: TyCtxt<'tcx>,
    funcs: &[(DefId, &mir::Body<'tcx>)],
) -> std::collections::HashMap<DefId, HeapSummary> {
    let in_crate: std::collections::HashSet<DefId> = funcs.iter().map(|(d, _)| *d).collect();
    let bodies: std::collections::HashMap<DefId, &mir::Body<'tcx>> = funcs.iter().map(|(d, b)| (*d, *b)).collect();

    let mut graph = std::collections::HashMap::new();
    for (d, body) in funcs {
        graph.insert(*d, summary::direct_callees(body, &in_crate));
    }

    let mut summaries = std::collections::HashMap::new();
    for d in summary::call_order(funcs, &graph) {
        let (_, _, sum) = analyze_fn(tcx, bodies[&d], &summaries);
        summaries.insert(d, sum);
    }
    summaries
}

fn dot_fn(tcx: TyCtxt<'_>, idx: usize, def_id: DefId, paths: &[Path<'_>], looped: bool, sym: Option<&Vec<String>>) {
    let sig = format!("{}({})", tcx.def_path_str(def_id), paths[0].1.params_str());
    if paths.len() == 1 {
        let note = looped.then_some("approximate: loops not modelled");
        paths[0].1.dot_cluster(idx, &sig, &paths[0].2, sym, note);
        return;
    }
    println!("  subgraph cluster_{idx} {{");
    println!("    label=\"{}\";", esc(&sig));
    println!("    h{idx} [shape=box, style=bold, label=\"returns {}\"];", esc(&recombine(paths, sym)));
    for (p, (guards, state, _)) in paths.iter().enumerate() {
        let cond = state.guard_cond(guards, sym);
        let cond = if cond.is_empty() { "default".to_string() } else { cond };
        println!("    subgraph cluster_{idx}_{p} {{");
        println!("      label=\"[{}]\\n{}\";", esc(&cond), esc(&state.ub_label()));
        state.dot_nodes(idx, Some(p), None);
        println!("    }}");
    }
    println!("  }}");
}

fn new_state<'tcx>(tcx: TyCtxt<'tcx>, body: &mir::Body<'tcx>) -> State<'tcx> {
    let names = summary::local_names(body);
    let muts = body.local_decls.iter().map(|d| matches!(d.mutability, mir::Mutability::Mut)).collect();
    let refs = body.local_decls.iter().map(|d| matches!(d.ty.kind(), ty::Ref(..) | ty::RawPtr(..))).collect();
    let n = body.local_decls.len();
    let mut s = State {
        tcx,
        typing_env: ty::TypingEnv::fully_monomorphized(),
        names,
        muts,
        refs,
        arg_count: body.arg_count,
        lifetimes: lifetimes(body),
        block_step: block_steps(body),
        heap: Vec::new(),
        vars: vec![None; n],
        step: 0,
        ub: Vec::new(),
    };
    s.seed_params(body);
    s
}

fn block_steps(body: &mir::Body<'_>) -> Vec<Step> {
    let mut base = Vec::with_capacity(body.basic_blocks.len());
    let mut step = 0;
    for data in body.basic_blocks.iter() {
        base.push(step);
        step += data.statements.len() + 1;
    }
    base
}

impl<'tcx> State<'tcx> {
    fn run_block_body(
        &mut self,
        body: &mir::Body<'tcx>,
        bb: mir::BasicBlock,
        summaries: &std::collections::HashMap<DefId, HeapSummary>,
    ) -> Option<Val> {
        let data = &body.basic_blocks[bb];
        self.step = self.block_step[bb.as_usize()];
        for stmt in &data.statements {
            if let mir::StatementKind::Assign(b) = &stmt.kind {
                let (place, rv) = &**b;
                if place.projection.is_empty() {
                    self.step_assign(place.local.as_usize(), rv);
                } else if single_deref(place) {
                    let v = self.eval(rv);
                    self.write_through(place.local.as_usize(), v);
                }
            }
            self.step += 1;
        }
        let ret = match &data.terminator().kind {
            mir::TerminatorKind::Call { func, args, destination, .. } if destination.projection.is_empty() => {
                let dest = destination.local.as_usize();
                match summary::callee_def_id(func).and_then(|d| summaries.get(&d)) {
                    Some(sum) => {
                        let actuals: Vec<(Val, Option<usize>)> = args
                            .iter()
                            .map(|a| {
                                let rl = self.ref_arg(&a.node);
                                let val = if rl.is_some() { Val::Unknown } else { self.operand(&a.node) };
                                (val, rl)
                            })
                            .collect();
                        self.instantiate(sum, &actuals, dest);
                    }
                    None => self.assign_owned(dest, Val::Unknown),
                }
                None
            }
            mir::TerminatorKind::Return => Some(self.read(0)),
            _ => None,
        };
        self.step += 1;
        ret
    }
}

fn analyze_fn<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &mir::Body<'tcx>,
    summaries: &std::collections::HashMap<DefId, HeapSummary>,
) -> (State<'tcx>, Val, HeapSummary) {
    let mut s = new_state(tcx, body);
    let mut ret = Val::Unit;
    for (bb, _) in body.basic_blocks.iter_enumerated() {
        if let Some(r) = s.run_block_body(body, bb, summaries) {
            ret = r;
        }
    }
    let summary = extract_summary(&s, ret.clone());
    (s, ret, summary)
}

#[derive(Clone)]
struct Guard {
    discr: Option<usize>,
    value: Option<i128>,
    is_bool: bool,
}

type Path<'tcx> = (Vec<Guard>, State<'tcx>, Val);

fn analyze_paths<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &mir::Body<'tcx>,
    summaries: &std::collections::HashMap<DefId, HeapSummary>,
) -> (Vec<Path<'tcx>>, bool) {
    let mut state = new_state(tcx, body);
    if summary::has_loop(body) {
        let mut ret = Val::Unit;
        for (bb, _) in body.basic_blocks.iter_enumerated() {
            if let Some(r) = state.run_block_body(body, bb, summaries) {
                ret = r;
            }
        }
        return (vec![(Vec::new(), state, ret)], true);
    }
    let mut out = Vec::new();
    walk_paths(state, mir::START_BLOCK, Vec::new(), body, summaries, &mut out);
    (out, false)
}

fn walk_paths<'tcx>(
    mut state: State<'tcx>,
    bb: mir::BasicBlock,
    guards: Vec<Guard>,
    body: &mir::Body<'tcx>,
    summaries: &std::collections::HashMap<DefId, HeapSummary>,
    out: &mut Vec<Path<'tcx>>,
) {
    let ret = state.run_block_body(body, bb, summaries);
    let term = body.basic_blocks[bb].terminator();
    match &term.kind {
        mir::TerminatorKind::Return => out.push((guards, state, ret.unwrap_or(Val::Unit))),
        mir::TerminatorKind::SwitchInt { discr, targets } => {
            let discr_local = operand_locals(discr);
            let is_bool = discr.ty(&body.local_decls, state.tcx).is_bool();
            for (v, t) in targets.iter() {
                let mut g = guards.clone();
                g.push(Guard { discr: discr_local, value: Some(v as i128), is_bool });
                walk_paths(state.clone(), t, g, body, summaries, out);
            }
            let mut g = guards;
            g.push(Guard { discr: discr_local, value: None, is_bool });
            walk_paths(state, targets.otherwise(), g, body, summaries, out);
        }
        _ => match term.successors().next() {
            Some(t) => walk_paths(state, t, guards, body, summaries, out),
            None => out.push((guards, state, ret.unwrap_or(Val::Unit))),
        },
    }
}

fn recombine(paths: &[Path<'_>], sym: Option<&Vec<String>>) -> String {
    let texts: Vec<String> = paths.iter().map(|(_, st, r)| st.fmt_val(r)).collect();
    if texts.windows(2).all(|w| w[0] == w[1]) {
        return texts[0].clone();
    }
    let (_, last_st, last_ret) = paths.last().unwrap();
    let mut acc = last_st.fmt_val(last_ret);
    for (g, st, r) in paths[..paths.len() - 1].iter().rev() {
        acc = format!("if {} {{ {} }} else {{ {} }}", st.guard_cond(g, sym), st.fmt_val(r), acc);
    }
    format!("({acc})")
}

fn report_fn(tcx: TyCtxt<'_>, def_id: DefId, paths: &[Path<'_>], looped: bool, sym: Option<&Vec<String>>) {
    println!("\nfn {}", tcx.def_path_str(def_id));
    if paths.len() == 1 {
        let note = looped.then_some("approximate: loops not modelled");
        paths[0].1.report_body(&paths[0].2, sym, "", note);
        return;
    }
    for (guards, state, ret) in paths {
        println!("  path [{}]:", state.guard_cond(guards, sym));
        state.report_body(ret, None, "  ", None);
    }
    println!("  summary: returns {}", recombine(paths, sym));
}

fn extract_summary(s: &State<'_>, ret: Val) -> HeapSummary {
    let is_ref = |o: &Ownership| matches!(o, Ownership::SharedRef(..) | Ownership::MutRef(..));
    let mut writes = Vec::new();
    for i in 1..=s.arg_count {
        if s.refs[i] {
            if let Some(own) = s.vars[i] {
                let v = &s.heap[own.addr()].value;
                if !matches!(v, Val::In(j) if *j == i - 1) {
                    writes.push((i - 1, v.clone()));
                }
            }
        }
    }
    let ret = (1..=s.arg_count)
        .find_map(|i| {
            let (v0, vi) = (s.vars[0]?, s.vars[i]?);
            (s.refs[i] && is_ref(&v0) && v0.addr() == vi.addr()).then_some(Ret::Ref(i - 1))
        })
        .unwrap_or(Ret::Val(ret));
    HeapSummary { writes, ret }
}

impl<'tcx> State<'tcx> {
    fn owner_of(&self, a: Addr) -> Option<usize> {
        (0..self.vars.len()).find(|&i| {
            matches!(self.vars[i], Some(Ownership::Owned(x, _)) | Some(Ownership::MutOwned(x, _)) if x == a)
        })
    }

    fn cell_text(&self, a: Addr, sym: Option<&Vec<String>>) -> String {
        match (sym, self.owner_of(a)) {
            (Some(s), Some(l)) => s.get(l).cloned().unwrap_or_else(|| self.fmt_val(&self.heap[a].value)),
            _ => self.fmt_val(&self.heap[a].value),
        }
    }

    fn ret_text(&self, ret: &Val, sym: Option<&Vec<String>>) -> String {
        match sym.and_then(|s| s.first()) {
            Some(v) if v != "?" => v.clone(),
            _ => self.fmt_val(ret),
        }
    }

    fn guard_cond(&self, guards: &[Guard], sym: Option<&Vec<String>>) -> String {
        guards.iter().map(|g| self.guard_one(g, sym)).collect::<Vec<_>>().join(" && ")
    }

    fn guard_one(&self, g: &Guard, sym: Option<&Vec<String>>) -> String {
        let name = match g.discr {
            Some(l) => sym
                .and_then(|s| s.get(l))
                .filter(|v| v.as_str() != "?")
                .cloned()
                .unwrap_or_else(|| self.names.get(l).cloned().unwrap_or_else(|| "?".into())),
            None => "?".into(),
        };
        match (g.is_bool, g.value) {
            (true, Some(0)) => format!("!{name}"),
            (true, _) => name,
            (false, Some(v)) => format!("{name} == {v}"),
            (false, None) => "else".into(),
        }
    }

    fn report_body(&self, ret: &Val, sym: Option<&Vec<String>>, indent: &str, note: Option<&str>) {
        let shown: Vec<usize> =
            (0..self.vars.len()).filter(|&i| self.vars[i].is_some() && !self.names[i].starts_with('_')).collect();
        let mut addrs: Vec<Addr> = shown.iter().filter_map(|&i| self.vars[i].map(|o| o.addr())).collect();
        addrs.sort_unstable();
        addrs.dedup();

        println!("{indent}  vars:");
        for &i in &shown {
            let own = self.vars[i].unwrap();
            let lt = own.lifetime();
            println!("{indent}    {:<6} {} @a{}  [lt{} {}..{}]", self.names[i], own.kind(), own.addr(), lt.id, lt.start, lt.end);
        }
        println!("{indent}  heap:");
        for a in addrs {
            println!("{indent}    a{a} = {}  ({})", self.cell_text(a, sym), self.heap[a].state.label());
        }
        let note = note.map(|n| format!("  ({n})")).unwrap_or_default();
        println!("{indent}  summary: returns {}{note}", self.ret_text(ret, sym));
        if self.ub.is_empty() {
            println!("{indent}  UB: none");
        } else {
            for msg in &self.ub {
                println!("{indent}  UB: {msg}");
            }
        }
    }

    fn params_str(&self) -> String {
        (1..=self.arg_count).map(|i| self.names[i].clone()).collect::<Vec<_>>().join(", ")
    }

    fn ub_label(&self) -> String {
        if self.ub.is_empty() {
            "UB: none".to_string()
        } else {
            self.ub.iter().map(|m| format!("UB: {m}")).collect::<Vec<_>>().join("\\n")
        }
    }

    fn dot_nodes(&self, idx: usize, path: Option<usize>, sym: Option<&Vec<String>>) {
        let shown: Vec<usize> =
            (0..self.vars.len()).filter(|&i| self.vars[i].is_some() && !self.names[i].starts_with('_')).collect();
        let mut addrs: Vec<Addr> = shown.iter().filter_map(|&i| self.vars[i].map(|o| o.addr())).collect();
        addrs.sort_unstable();
        addrs.dedup();

        let cid = |a: Addr| match path {
            Some(p) => format!("c{idx}_{p}_{a}"),
            None => format!("c{idx}_{a}"),
        };
        let vid = |i: usize| match path {
            Some(p) => format!("v{idx}_{p}_{i}"),
            None => format!("v{idx}_{i}"),
        };
        for &a in &addrs {
            println!("    {} [label=\"a{a} = {}\\n{}\"];", cid(a), esc(&self.cell_text(a, sym)), esc(&self.heap[a].state.label()));
        }
        for &i in &shown {
            let own = self.vars[i].unwrap();
            let lt = own.lifetime();
            println!("    {} [style=rounded, label=\"{}\\n[lt{} {}..{}]\"];", vid(i), esc(&self.names[i]), lt.id, lt.start, lt.end);
            let dashed = if matches!(own, Ownership::SharedRef(..) | Ownership::MutRef(..)) { ", style=dashed" } else { "" };
            println!("    {} -> {} [label=\"{}\"{dashed}];", vid(i), cid(own.addr()), own.kind());
        }
    }

    fn dot_cluster(&self, idx: usize, sig: &str, ret: &Val, sym: Option<&Vec<String>>, note: Option<&str>) {
        let ret_note = note.map(|n| format!("\\n({n})")).unwrap_or_default();
        println!("  subgraph cluster_{idx} {{");
        println!(
            "    h{idx} [shape=box, style=bold, label=\"{}\\nreturns {}{}\\n{}\"];",
            esc(sig),
            esc(&self.ret_text(ret, sym)),
            ret_note,
            esc(&self.ub_label())
        );
        self.dot_nodes(idx, None, sym);
        println!("  }}");
    }
}

fn esc(s: &str) -> String {
    s.replace('\\', "\\\\").replace('"', "\\\"")
}

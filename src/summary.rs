//! A first step toward a function summary: give each local a symbolic value and
//! report what the function returns in terms of its inputs.

use rustc_middle::mir;
use rustc_middle::ty::{self, TyCtxt};

use crate::walk::{self, Visitor};

#[derive(Clone, PartialEq)]
enum Sym {
    Input(String),
    Const(i128),
    Bin(String, Box<Sym>, Box<Sym>),
    Un(String, Box<Sym>),
    /// A value chosen by a branch: `if cond { then } else { els }`.
    Cond(Box<Sym>, Box<Sym>, Box<Sym>),
    /// A reference to a local: `target` is which local, `name` is just for display.
    Ref { target: usize, name: String },
    /// The result of calling `name` with the given argument values.
    Call(String, Vec<Sym>),
    /// A field read off another value: `base.name`.
    Field(Box<Sym>, String),
    /// A composite built in place — struct/tuple/array fields in declaration order.
    Aggregate(Vec<Sym>),
    /// An indexed read: `base[idx]`.
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

/// Is this place a single `*p` (one Deref, nothing else)?
fn single_deref(p: &mir::Place<'_>) -> bool {
    p.projection.len() == 1 && matches!(p.projection[0], mir::ProjectionElem::Deref)
}

struct Summary<'tcx> {
    tcx: TyCtxt<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    names: Vec<String>,
    tys: Vec<ty::Ty<'tcx>>,
    env: Vec<Sym>,
}

impl<'tcx> Visitor<'tcx> for Summary<'tcx> {
    fn statement(&mut self, stmt: &mir::Statement<'tcx>) {
        if let mir::StatementKind::Assign(b) = &stmt.kind {
            let (place, rv) = &**b;
            let v = self.rvalue(rv);
            let dest = place.local.as_usize();
            if place.projection.is_empty() {
                self.env[dest] = v;
            } else if single_deref(place) {
                // `*p = v`: if p is a known reference, update what it points at.
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
            // The return value lands in `destination` once the call returns.
            if destination.projection.is_empty() {
                let dest = destination.local.as_usize();
                self.env[dest] = match self.callee_name(func) {
                    Some(name) => {
                        let args = args.iter().map(|a| self.operand(&a.node)).collect();
                        Sym::Call(name, args)
                    }
                    None => Sym::Unknown,
                };
            }
        }
    }
}

impl<'tcx> Summary<'tcx> {
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

    /// The short name of a directly-called function, if `func` is a `FnDef` constant.
    fn callee_name(&self, func: &mir::Operand<'tcx>) -> Option<String> {
        let c = match func {
            mir::Operand::Constant(c) => c,
            _ => return None, // indirect call through a fn pointer: name unknown
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

    /// The symbolic value read from a place: a bare local, `*p` when `p` is a known
    /// reference, or `base.field` for a single field access.
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
                // Reading a field off a composite we built: hand back that field's value.
                Sym::Aggregate(elems) => elems.into_iter().nth(i).unwrap_or(Sym::Unknown),
                Sym::Unknown => Sym::Unknown,
                base => Sym::Field(Box::new(base), self.field_name(self.tys[local], i)),
            }
        } else if let [mir::ProjectionElem::Index(li)] = &p.projection[..] {
            // `a[i]`: the index lives in its own local, often a known constant.
            index_into(self.env[local].clone(), self.env[li.as_usize()].clone())
        } else if let [mir::ProjectionElem::ConstantIndex { offset, from_end: false, .. }] =
            &p.projection[..]
        {
            index_into(self.env[local].clone(), Sym::Const(*offset as i128))
        } else {
            Sym::Unknown
        }
    }

    /// The source name of field `idx` of `base_ty`, falling back to its position for
    /// tuples or anything that isn't a struct.
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

/// Index into a value. A known aggregate at a known in-range constant resolves to that
/// element; otherwise it stays the symbolic read `base[idx]`.
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

/// Build a binary expression, folding it to a constant when both sides are known.
fn mk_bin(op: &mir::BinOp, l: Sym, r: Sym) -> Sym {
    if let (Sym::Const(a), Sym::Const(b)) = (&l, &r) {
        if let Some(v) = fold_bin(op, *a, *b) {
            return Sym::Const(v);
        }
    }
    Sym::Bin(bin_op(op), Box::new(l), Box::new(r))
}

/// Build a unary expression, folding negation of a known constant.
fn mk_un(op: &mir::UnOp, v: Sym) -> Sym {
    if let (mir::UnOp::Neg, Sym::Const(a)) = (op, &v) {
        if let Some(n) = a.checked_neg() {
            return Sym::Const(n);
        }
    }
    Sym::Un(un_op(op), Box::new(v))
}

/// Evaluate `a op b` over i128, or `None` when the result isn't well-defined here
/// (overflow, divide-by-zero, an out-of-range shift, or an op we don't fold).
/// Comparisons fold to 1/0. Widths aren't tracked, so wrapping isn't modelled.
fn fold_bin(op: &mir::BinOp, a: i128, b: i128) -> Option<i128> {
    use mir::BinOp::*;
    let shift = |amt: i128| (0..128).contains(&amt).then_some(amt as u32);
    match op {
        Add | AddUnchecked | AddWithOverflow => a.checked_add(b),
        Sub | SubUnchecked | SubWithOverflow => a.checked_sub(b),
        Mul | MulUnchecked | MulWithOverflow => a.checked_mul(b),
        Div => a.checked_div(b),
        Rem => a.checked_rem(b),
        BitXor => Some(a ^ b),
        BitAnd => Some(a & b),
        BitOr => Some(a | b),
        Shl | ShlUnchecked => shift(b).and_then(|s| a.checked_shl(s)),
        Shr | ShrUnchecked => shift(b).and_then(|s| a.checked_shr(s)),
        Eq => Some((a == b) as i128),
        Ne => Some((a != b) as i128),
        Lt => Some((a < b) as i128),
        Le => Some((a <= b) as i128),
        Gt => Some((a > b) as i128),
        Ge => Some((a >= b) as i128),
        _ => None,
    }
}

fn bin_op(op: &mir::BinOp) -> String {
    use mir::BinOp::*;
    // Unchecked/WithOverflow variants are the same operation as their plain form at
    // the source level, so they share a symbol.
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

/// Source name of each local from MIR debug info, falling back to `_N`.
fn local_names(body: &mir::Body<'_>) -> Vec<String> {
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

/// Why control reached a block, so a join can rebuild the branch it came from.
#[derive(Clone)]
enum Guard {
    /// taken because the switch discriminant equalled this value
    Eq(Sym, i128),
    /// taken because none of the listed values matched
    Otherwise(Sym),
}

pub fn run<'tcx>(tcx: TyCtxt<'tcx>, body: &mir::Body<'tcx>) {
    let names = local_names(body);
    let tys = body.local_decls.iter().map(|d| d.ty).collect();
    let mut init = vec![Sym::Unknown; body.local_decls.len()];
    for i in 1..=body.arg_count {
        init[i] = Sym::Input(names[i].clone());
    }
    let mut s = Summary { tcx, typing_env: ty::TypingEnv::fully_monomorphized(), names, tys, env: init.clone() };

    // Walk the blocks in an order where each comes after its predecessors, merging
    // branches back together at joins. A loop has no such order, so fall back to a
    // straight-line walk and admit it's approximate.
    match topo_order(body) {
        Some(order) => match s.eval_cfg(body, &order, init) {
            (val, false) => println!("  summary: returns {val}"),
            (val, true) => println!("  summary: returns {val}  (approximate)"),
        },
        None => {
            s.env = init;
            walk::walk(body, &mut s);
            println!("  summary: returns {}  (approximate: loops not modelled)", s.env[0]);
        }
    }
}

impl<'tcx> Summary<'tcx> {
    /// Evaluate the body block by block in `order`, computing each block's entry from
    /// its predecessors' exits and merging differing values into a branch. Returns the
    /// final value of `_0` and whether any merge had to give up and approximate.
    fn eval_cfg(&mut self, body: &mir::Body<'tcx>, order: &[mir::BasicBlock], init: Vec<Sym>) -> (Sym, bool) {
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
                    // Carry this block's guard down a straight chain so it survives to
                    // the next join; a join sets its own guard, so don't overwrite it.
                    for succ in term.successors() {
                        if preds[succ].len() == 1 {
                            guard[succ.as_usize()] = guard[bb.as_usize()].clone();
                        }
                    }
                }
            }
        }

        match returns.as_slice() {
            [only] => (only[0].clone(), imprecise),
            [first, rest @ ..] if rest.iter().all(|e| e[0] == first[0]) => (first[0].clone(), imprecise),
            _ => (Sym::Unknown, true),
        }
    }
}

/// Merge the exit states of several predecessors into one entry state. Where they
/// agree the value carries through; where exactly two disagree and their guards are
/// the two sides of one branch, rebuild that branch. Anything else gives up.
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

/// Rebuild `if cond { .. } else { .. }` from the two arms of a branch, given each
/// arm's value and the guard that selected it. `None` if the guards aren't a matching
/// equal/otherwise pair on one discriminant.
fn branch_value(va: &Sym, ga: Option<&Guard>, vb: &Sym, gb: Option<&Guard>) -> Option<Sym> {
    // Order the arms so `eq` is the `discr == value` side and `oth` is the fallthrough.
    let (d, val, eq_val, oth_val) = match (ga?, gb?) {
        (Guard::Eq(d1, v), Guard::Otherwise(d2)) if d1 == d2 => (d1, *v, va, vb),
        (Guard::Otherwise(d2), Guard::Eq(d1, v)) if d1 == d2 => (d1, *v, vb, va),
        _ => return None,
    };
    if val == 0 {
        // A bool: `discr == 0` is the `else`, so the discriminant itself is the test.
        Some(Sym::Cond(Box::new(d.clone()), Box::new(oth_val.clone()), Box::new(eq_val.clone())))
    } else {
        let cond = Sym::Bin("==".into(), Box::new(d.clone()), Box::new(Sym::Const(val)));
        Some(Sym::Cond(Box::new(cond), Box::new(eq_val.clone()), Box::new(oth_val.clone())))
    }
}

/// Order the blocks so every block comes after all its predecessors (reverse
/// postorder). Returns `None` if there's a back edge, i.e. a loop.
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
                Some(Mark::Open) => return None, // back edge: a loop
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

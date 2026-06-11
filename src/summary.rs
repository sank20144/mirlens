//! A first step toward a function summary: give each local a symbolic value and
//! report what the function returns in terms of its inputs.

use rustc_middle::mir;
use rustc_middle::ty::{self, TyCtxt};

use crate::walk::{self, Visitor};

#[derive(Clone)]
enum Sym {
    Input(String),
    Const(i128),
    Bin(String, Box<Sym>, Box<Sym>),
    Un(String, Box<Sym>),
    /// A reference to a local: `target` is which local, `name` is just for display.
    Ref { target: usize, name: String },
    Unknown,
}

impl std::fmt::Display for Sym {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Sym::Input(name) => write!(f, "{name}"),
            Sym::Const(v) => write!(f, "{v}"),
            Sym::Bin(op, l, r) => write!(f, "({l} {op} {r})"),
            Sym::Un(op, v) => write!(f, "{op}{v}"),
            Sym::Ref { name, .. } => write!(f, "&{name}"),
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
            _ => Sym::Unknown,
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

    /// The symbolic value read from a place: a bare local, or `*p` when `p` is a known reference.
    fn place_value(&self, p: &mir::Place<'tcx>) -> Sym {
        if p.projection.is_empty() {
            self.env[p.local.as_usize()].clone()
        } else if single_deref(p) {
            match &self.env[p.local.as_usize()] {
                Sym::Ref { target, .. } => self.env[*target].clone(),
                _ => Sym::Unknown,
            }
        } else {
            Sym::Unknown
        }
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

pub fn run<'tcx>(tcx: TyCtxt<'tcx>, body: &mir::Body<'tcx>) {
    let names = local_names(body);
    let mut env = vec![Sym::Unknown; body.local_decls.len()];
    for i in 1..=body.arg_count {
        env[i] = Sym::Input(names[i].clone());
    }
    let mut s = Summary { tcx, typing_env: ty::TypingEnv::fully_monomorphized(), names, env };
    walk::walk(body, &mut s);
    println!("  summary: returns {}", s.env[0]);
}

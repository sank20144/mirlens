//! A first step toward a function summary: give each local a symbolic value and
//! report what the function returns in terms of its inputs.

use rustc_middle::mir;
use rustc_middle::ty::{self, TyCtxt};

use crate::walk::{self, Visitor};

#[derive(Clone)]
enum Sym {
    Input(String),
    Const(i128),
    Unknown,
}

impl std::fmt::Display for Sym {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Sym::Input(name) => write!(f, "{name}"),
            Sym::Const(v) => write!(f, "{v}"),
            Sym::Unknown => write!(f, "?"),
        }
    }
}

struct Summary<'tcx> {
    tcx: TyCtxt<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    env: Vec<Sym>,
}

impl<'tcx> Visitor<'tcx> for Summary<'tcx> {
    fn statement(&mut self, stmt: &mir::Statement<'tcx>) {
        if let mir::StatementKind::Assign(b) = &stmt.kind {
            let (place, rv) = &**b;
            if place.projection.is_empty() {
                self.env[place.local.as_usize()] = self.rvalue(rv);
            }
        }
    }
}

impl<'tcx> Summary<'tcx> {
    fn rvalue(&self, rv: &mir::Rvalue<'tcx>) -> Sym {
        match rv {
            mir::Rvalue::Use(op, _) => self.operand(op),
            _ => Sym::Unknown,
        }
    }

    fn operand(&self, op: &mir::Operand<'tcx>) -> Sym {
        match op {
            mir::Operand::Copy(p) | mir::Operand::Move(p) if p.projection.is_empty() => {
                self.env[p.local.as_usize()].clone()
            }
            mir::Operand::Constant(c) => match c.const_.try_eval_bits(self.tcx, self.typing_env) {
                Some(bits) => Sym::Const(bits as i128),
                None => Sym::Unknown,
            },
            _ => Sym::Unknown,
        }
    }
}

pub fn run<'tcx>(tcx: TyCtxt<'tcx>, body: &mir::Body<'tcx>) {
    let mut env = vec![Sym::Unknown; body.local_decls.len()];
    for i in 1..=body.arg_count {
        env[i] = Sym::Input(format!("_{i}"));
    }
    let mut s = Summary { tcx, typing_env: ty::TypingEnv::fully_monomorphized(), env };
    walk::walk(body, &mut s);
    println!("  summary: returns {}", s.env[0]);
}

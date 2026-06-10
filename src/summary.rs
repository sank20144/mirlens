//! A first step toward a function summary: give each local a symbolic value and
//! report what the function returns in terms of its inputs.

use rustc_middle::mir;

use crate::walk::{self, Visitor};

#[derive(Clone)]
enum Sym {
    Input(String),
    Unknown,
}

impl std::fmt::Display for Sym {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Sym::Input(name) => write!(f, "{name}"),
            Sym::Unknown => write!(f, "?"),
        }
    }
}

struct Summary {
    env: Vec<Sym>,
}

impl Visitor for Summary {
    fn statement(&mut self, stmt: &mir::Statement<'_>) {
        if let mir::StatementKind::Assign(b) = &stmt.kind {
            let (place, rv) = &**b;
            if place.projection.is_empty() {
                self.env[place.local.as_usize()] = self.rvalue(rv);
            }
        }
    }
}

impl Summary {
    fn rvalue(&self, rv: &mir::Rvalue<'_>) -> Sym {
        match rv {
            mir::Rvalue::Use(op, _) => self.operand(op),
            _ => Sym::Unknown,
        }
    }

    fn operand(&self, op: &mir::Operand<'_>) -> Sym {
        match op {
            mir::Operand::Copy(p) | mir::Operand::Move(p) if p.projection.is_empty() => {
                self.env[p.local.as_usize()].clone()
            }
            _ => Sym::Unknown,
        }
    }
}

pub fn run<'tcx>(body: &mir::Body<'tcx>) {
    let mut env = vec![Sym::Unknown; body.local_decls.len()];
    for i in 1..=body.arg_count {
        env[i] = Sym::Input(format!("_{i}"));
    }
    let mut s = Summary { env };
    walk::walk(body, &mut s);
    println!("  summary: returns {}", s.env[0]);
}

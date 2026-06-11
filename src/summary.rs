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
    Unknown,
}

impl std::fmt::Display for Sym {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Sym::Input(name) => write!(f, "{name}"),
            Sym::Const(v) => write!(f, "{v}"),
            Sym::Bin(op, l, r) => write!(f, "({l} {op} {r})"),
            Sym::Un(op, v) => write!(f, "{op}{v}"),
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
            mir::Rvalue::BinaryOp(op, b) => {
                let (l, r) = &**b;
                Sym::Bin(bin_op(op), Box::new(self.operand(l)), Box::new(self.operand(r)))
            }
            mir::Rvalue::UnaryOp(op, operand) => Sym::Un(un_op(op), Box::new(self.operand(operand))),
            mir::Rvalue::Cast(_, operand, _) => self.operand(operand),
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

fn bin_op(op: &mir::BinOp) -> String {
    match op {
        mir::BinOp::Add => "+".into(),
        mir::BinOp::Sub => "-".into(),
        mir::BinOp::Mul => "*".into(),
        other => format!("{other:?}"),
    }
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
    let mut s = Summary { tcx, typing_env: ty::TypingEnv::fully_monomorphized(), env };
    walk::walk(body, &mut s);
    println!("  summary: returns {}", s.env[0]);
}

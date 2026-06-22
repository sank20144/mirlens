use rustc_hir::def_id::DefId;
use rustc_middle::mir;
use rustc_middle::ty::TyCtxt;

pub trait Visitor<'tcx> {
    fn block(&mut self, _bb: mir::BasicBlock) {}
    fn statement(&mut self, _stmt: &mir::Statement<'tcx>) {}
    fn terminator(&mut self, _term: &mir::Terminator<'tcx>) {}
}

pub fn walk<'tcx>(body: &mir::Body<'tcx>, v: &mut impl Visitor<'tcx>) {
    for (bb, data) in body.basic_blocks.iter_enumerated() {
        v.block(bb);
        for stmt in &data.statements {
            v.statement(stmt);
        }
        v.terminator(data.terminator());
    }
}

pub fn body_lines<'tcx>(body: &mir::Body<'tcx>) -> Vec<String> {
    let mut p = Printer { out: Vec::new() };
    for (local, decl) in body.local_decls.iter_enumerated() {
        let kw = if matches!(decl.mutability, mir::Mutability::Mut) { "mut " } else { "" };
        p.out.push(format!("let {kw}{local:?}: {}", decl.ty));
    }
    walk(body, &mut p);
    p.out
}

pub fn body<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId, body: &mir::Body<'tcx>) {
    println!("\nfn {}", tcx.def_path_str(def_id));
    for line in body_lines(body) {
        println!("  {line}");
    }
}

struct Printer {
    out: Vec<String>,
}

impl<'tcx> Visitor<'tcx> for Printer {
    fn block(&mut self, bb: mir::BasicBlock) {
        self.out.push(format!("{bb:?}:"));
    }

    fn statement(&mut self, stmt: &mir::Statement<'tcx>) {
        use mir::StatementKind::*;
        match &stmt.kind {
            Assign(b) => {
                let (place, rv) = &**b;
                self.out.push(format!("  {place:?} ="));
                self.rvalue(rv);
            }
            StorageLive(l) => self.out.push(format!("  StorageLive({l:?})")),
            StorageDead(l) => self.out.push(format!("  StorageDead({l:?})")),
            other => self.out.push(format!("  {other:?}")),
        }
    }

    fn terminator(&mut self, term: &mir::Terminator<'tcx>) {
        use mir::TerminatorKind::*;
        match &term.kind {
            Goto { target } => self.out.push(format!("  goto -> {target:?}")),
            SwitchInt { discr, .. } => self.out.push(format!("  switchInt({discr:?})")),
            Call { func, .. } => self.out.push(format!("  call {func:?}")),
            Drop { place, .. } => self.out.push(format!("  drop({place:?})")),
            Return => self.out.push("  return".into()),
            other => self.out.push(format!("  {other:?}")),
        }
    }
}

impl Printer {
    fn rvalue(&mut self, rv: &mir::Rvalue<'_>) {
        use mir::Rvalue::*;
        match rv {
            Use(op, _) => self.operand(op),
            Ref(_, _, place) => self.out.push(format!("    &{place:?}")),
            BinaryOp(op, b) => {
                self.out.push(format!("    {op:?}"));
                self.operand(&b.0);
                self.operand(&b.1);
            }
            other => self.out.push(format!("    {other:?}")),
        }
    }

    fn operand(&mut self, op: &mir::Operand<'_>) {
        match op {
            mir::Operand::Copy(p) => self.out.push(format!("    copy {p:?}")),
            mir::Operand::Move(p) => self.out.push(format!("    move {p:?}")),
            mir::Operand::Constant(c) => self.out.push(format!("    const {:?}", c.const_)),
            _ => {}
        }
    }
}

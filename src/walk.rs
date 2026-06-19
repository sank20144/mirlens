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

pub fn body<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId, body: &mir::Body<'tcx>) {
    println!("\nfn {}", tcx.def_path_str(def_id));
    for (local, decl) in body.local_decls.iter_enumerated() {
        let kw = if matches!(decl.mutability, mir::Mutability::Mut) { "mut " } else { "" };
        println!("  let {kw}{local:?}: {}", decl.ty);
    }
    walk(body, &mut Printer);
}

struct Printer;

impl<'tcx> Visitor<'tcx> for Printer {
    fn block(&mut self, bb: mir::BasicBlock) {
        println!("  {bb:?}:");
    }

    fn statement(&mut self, stmt: &mir::Statement<'tcx>) {
        use mir::StatementKind::*;
        match &stmt.kind {
            Assign(b) => {
                let (place, rv) = &**b;
                println!("    {place:?} =");
                rvalue(rv);
            }
            StorageLive(l) => println!("    StorageLive({l:?})"),
            StorageDead(l) => println!("    StorageDead({l:?})"),
            other => println!("    {other:?}"),
        }
    }

    fn terminator(&mut self, term: &mir::Terminator<'tcx>) {
        use mir::TerminatorKind::*;
        match &term.kind {
            Goto { target } => println!("    goto -> {target:?}"),
            SwitchInt { discr, .. } => println!("    switchInt({discr:?})"),
            Call { func, .. } => println!("    call {func:?}"),
            Drop { place, .. } => println!("    drop({place:?})"),
            Return => println!("    return"),
            other => println!("    {other:?}"),
        }
    }
}

fn rvalue(rv: &mir::Rvalue<'_>) {
    use mir::Rvalue::*;
    match rv {
        Use(op, _) => operand(op),
        Ref(_, _, place) => println!("      &{place:?}"),
        BinaryOp(op, b) => {
            println!("      {op:?}");
            operand(&b.0);
            operand(&b.1);
        }
        other => println!("      {other:?}"),
    }
}

fn operand(op: &mir::Operand<'_>) {
    match op {
        mir::Operand::Copy(p) => println!("      copy {p:?}"),
        mir::Operand::Move(p) => println!("      move {p:?}"),
        mir::Operand::Constant(c) => println!("      const {:?}", c.const_),
        _ => {}
    }
}

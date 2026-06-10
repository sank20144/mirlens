//! Walks a function's MIR: blocks, then the statements and terminator in each,
//! down into the rvalues and operands.

use rustc_hir::def_id::DefId;
use rustc_middle::mir;
use rustc_middle::ty::TyCtxt;

pub fn body<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId, body: &mir::Body<'tcx>) {
    println!("\nfn {}", tcx.def_path_str(def_id));
    for (local, decl) in body.local_decls.iter_enumerated() {
        let kw = if matches!(decl.mutability, mir::Mutability::Mut) { "mut " } else { "" };
        println!("  let {kw}{local:?}: {}", decl.ty);
    }
    for (bb, data) in body.basic_blocks.iter_enumerated() {
        println!("  {bb:?}:");
        for stmt in &data.statements {
            statement(stmt);
        }
        terminator(data.terminator());
    }
}

fn statement(stmt: &mir::Statement<'_>) {
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

fn terminator(term: &mir::Terminator<'_>) {
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

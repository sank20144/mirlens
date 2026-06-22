use std::collections::{HashMap, HashSet};

use rustc_hir::def_id::DefId;
use rustc_middle::mir;
use rustc_middle::ty;

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

#![feature(rustc_private)]

extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_session;

use std::process::Command;

use rustc_driver::{Callbacks, Compilation};
use rustc_hir::def::DefKind;
use rustc_interface::interface;
use rustc_middle::ty::TyCtxt;

mod heap;
mod mir_util;
mod walk;

struct Driver {
    dot: bool,
    heap: bool,
}

impl Callbacks for Driver {
    fn after_analysis<'tcx>(&mut self, _c: &interface::Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        let mut funcs = Vec::new();
        for &id in tcx.mir_keys(()).iter() {
            let def_id = id.to_def_id();
            if !tcx.is_mir_available(def_id) {
                continue;
            }
            if !matches!(tcx.def_kind(def_id), DefKind::Fn | DefKind::AssocFn | DefKind::Closure) {
                continue;
            }
            funcs.push((def_id, tcx.optimized_mir(def_id)));
        }

        if self.heap {
            if self.dot {
                heap::emit_dot(tcx, &funcs);
            } else {
                heap::analyze_crate(tcx, &funcs);
            }
        } else {
            for (def_id, body) in &funcs {
                walk::body(tcx, *def_id, body);
            }
        }
        Compilation::Stop
    }
}

fn sysroot() -> String {
    let rustc = std::env::var("RUSTC").unwrap_or_else(|_| "rustc".into());
    let out = Command::new(rustc).arg("--print=sysroot").output().unwrap();
    String::from_utf8(out.stdout).unwrap().trim().to_string()
}

fn main() {
    let mut args: Vec<String> = std::env::args().collect();
    let dot = args.iter().any(|a| a == "--dot");
    let heap = args.iter().any(|a| a == "--heap");
    args.retain(|a| a != "--dot" && a != "--heap");

    if !args.iter().any(|a| a.starts_with("--sysroot")) {
        args.push("--sysroot".into());
        args.push(sysroot());
    }

    args.push("-Cdebug-assertions=off".into());
    args.push("-Zmir-opt-level=0".into());
    args.push("-Zmir-preserve-ub".into());
    args.push("-Zub-checks=yes".into());
    args.push("-Zalways-encode-mir".into());

    rustc_driver::run_compiler(&args, &mut Driver { dot, heap });
}

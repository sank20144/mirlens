//! Minimal rustc driver. Compiles the input, grabs each function's MIR, and
//! passes it to `analyze`. Fill in `analyze` to do something with it.
//!
//!   mirlens --edition 2021 --crate-type lib path/to/file.rs
#![feature(rustc_private)]

extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_session;

use std::process::Command;

use rustc_driver::{Callbacks, Compilation};
use rustc_hir::def::DefKind;
use rustc_hir::def_id::DefId;
use rustc_interface::interface;
use rustc_middle::mir;
use rustc_middle::ty::TyCtxt;

/// Called once per function, with its MIR.
fn analyze<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId, body: &mir::Body<'tcx>) {
    println!("\n// MIR for {}", tcx.def_path_str(def_id));
    let mut out = Vec::new();
    mir::pretty::MirWriter::new(tcx).write_mir_fn(body, &mut out).unwrap();
    println!("{}", String::from_utf8_lossy(&out));
}

struct Driver;

impl Callbacks for Driver {
    fn after_analysis<'tcx>(&mut self, _c: &interface::Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        for &id in tcx.mir_keys(()).iter() {
            let def_id = id.to_def_id();
            // Skip consts/statics: optimized_mir panics on them.
            if !tcx.is_mir_available(def_id) {
                continue;
            }
            if !matches!(tcx.def_kind(def_id), DefKind::Fn | DefKind::AssocFn | DefKind::Closure) {
                continue;
            }
            analyze(tcx, def_id, tcx.optimized_mir(def_id));
        }
        Compilation::Stop // we want the MIR, not a binary
    }
}

fn sysroot() -> String {
    let rustc = std::env::var("RUSTC").unwrap_or_else(|_| "rustc".into());
    let out = Command::new(rustc).arg("--print=sysroot").output().unwrap();
    String::from_utf8(out.stdout).unwrap().trim().to_string()
}

fn main() {
    let mut args: Vec<String> = std::env::args().collect();
    if !args.iter().any(|a| a.starts_with("--sysroot")) {
        args.push("--sysroot".into());
        args.push(sysroot());
    }

    // release cfg, unoptimized MIR (so UB and StorageLive/StorageDead survive), MIR for all items.
    args.push("-Cdebug-assertions=off".into());
    args.push("-Zmir-opt-level=0".into());
    args.push("-Zmir-preserve-ub".into());
    args.push("-Zub-checks=yes".into());
    args.push("-Zalways-encode-mir".into());

    rustc_driver::run_compiler(&args, &mut Driver);
}

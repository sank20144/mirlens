# mirlens

A minimal custom `rustc` driver. It compiles a Rust file, pulls the MIR of every
function, and hands each one to `analyze` in `src/main.rs`. `analyze` currently
just prints the MIR — it's the single hook for building an analysis on top.

The driver runs the compiler as a library (`rustc_private`) and stops right after
analysis, so it never produces a binary. It compiles with MIR optimizations off
and UB checks preserved, which keeps the MIR faithful to what the source says.

## Build

`rust-toolchain.toml` pins the nightly (with `rustc-dev`), so `rustup` picks it
up automatically.

    cargo build

## Run

Pass a Rust file plus the usual rustc flags:

    target/debug/mirlens --edition 2021 --crate-type lib path/to/file.rs

The driver prints the MIR of each function in the file.

## Extending

`analyze(tcx, def_id, body)` gets one function's MIR at a time. Everything else
is just driver plumbing.

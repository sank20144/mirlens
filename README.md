# mirlens

A custom `rustc` driver that reads the MIR of every function in a crate and runs
a small analysis over it.

For each function it:

- **walks the MIR** — basic blocks, their statements and terminator, down into
  the rvalues and operands (`src/walk.rs`), and
- **prints a rough symbolic summary** — gives each parameter a symbolic value
  (named from debug info) and reports what the function returns in terms of those
  inputs: it folds in constants, builds arithmetic and unary expressions, and
  follows simple references — `&x`, and reads/writes through `*p` (`src/summary.rs`).

So `fn f(x: i32) -> i32 { x * 2 + 1 }` reports `returns ((x * 2) + 1)`, and
`fn h() { let mut x = 1; let r = &mut x; *r = 7; x }` reports `returns 7`.

The driver runs the compiler as a library (`rustc_private`) and stops right after
analysis, so it never produces a binary. It keeps the MIR unoptimized with UB
checks preserved, so the MIR stays faithful to what the source says.

## Build

`rust-toolchain.toml` pins the nightly (with `rustc-dev`), so `rustup` picks it
up automatically.

    cargo build

## Run

Pass a Rust file plus the usual rustc flags:

    target/debug/mirlens --edition 2021 --crate-type lib path/to/file.rs

## How it's put together

- `src/main.rs` — the driver: hooks rustc and hands each function's MIR to `analyze`.
- `src/walk.rs` — a `Visitor` trait and a `walk` that drives it over a body; the
  default `Printer` is what prints the MIR.
- `src/summary.rs` — a `Visitor` that builds a symbolic value per local.

Implement `Visitor` and call `walk` to plug in your own analysis.

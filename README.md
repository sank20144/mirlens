# mirlens

A custom `rustc` driver that reads the MIR of every function in a crate and runs
a heap/borrow safety model over it.

## Build

`rust-toolchain.toml` pins the nightly (with `rustc-dev`), so `rustup` picks it
up automatically.

    cargo build

## Run

Pass a Rust file plus the usual rustc flags.

Plain MIR dump (no analysis):

    target/debug/mirlens --edition 2021 --crate-type lib path/to/file.rs

Heap model. For each function it prints the Rust source, its MIR beside it, and the resulting heap (variables, cells, borrow state) per control-flow path:

    target/debug/mirlens --heap --edition 2021 --crate-type lib samples/ref_write.rs

Add `--dot` to draw the heaps and call graph as Graphviz, then pipe to `dot`:

    target/debug/mirlens --heap --dot --edition 2021 --crate-type lib samples/ref_write.rs | dot -Tsvg -o heap.svg

## Samples

`samples/` holds small programs to try. Run one, or all of them:

    for s in samples/*.rs; do target/debug/mirlens --heap --edition 2021 --crate-type lib "$s"; done

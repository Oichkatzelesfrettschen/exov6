# Rust Capability Example

This directory contains a minimal Rust crate demonstrating how to call
Phoenix kernel primitives directly. The bindings in `src/lib.rs` expose
`exo_alloc_page`, `exo_send` and `exo_yield_to` using `extern "C"`.
`src/main.rs` allocates a page, sends a short message and then yields to
that capability.

Build the binary with cargo using the cross toolchain installed by
`setup.sh`:

```bash
rustup target add x86_64-unknown-elf
RUSTFLAGS="-C linker=x86_64-elf-gcc" \
    cargo build --release --target x86_64-unknown-elf
```

The resulting executable can be copied into the filesystem image just
like the C demos.

# Phoenix POSIX User Guide

This guide explains how to build the Phoenix kernel, compile programs that use the libOS, and how the capability system maps to familiar POSIX interfaces. It supplements the more detailed [phoenixkernel.md](phoenixkernel.md) design notes.

## Building the Kernel and LibOS

Set up a build directory with Meson and compile everything with:

```sh
meson setup build && ninja -C build
```

This command generates the kernel image, user programs and `libos.a`.
If you prefer CMake for integration with other tools you can run:

```sh
cmake -S . -B build -G Ninja && ninja -C build
```

but note that the CMake configuration only builds a subset of the user
programs.

## Compiling Applications

Sources for user programs live under `demos`. Add the new
`*_prog` entry to `meson.build` (and to `engine/user/CMakeLists.txt`
if you are using the CMake configuration) then rebuild. A minimal file
reader looks like:

```c
#include "posix.h"
#include <fcntl.h>

int main(void) {
    int fd = libos_open("/hello.txt", O_RDONLY);
    char buf[32];
    int n = libos_read(fd, buf, sizeof(buf));
    libos_close(fd);
    write(1, buf, n);
    return 0;
}
```

The behaviour of `read()` matches the Single UNIX Specification; see [`ben-books/susv4-2018/functions/read.html`](ben-books/susv4-2018/functions/read.html) in the repository for the normative text.

## Capabilities and POSIX Semantics

Phoenix exposes low level capabilities such as pages, blocks and endpoints. The libOS translates these primitives into standard file descriptors and process IDs. For example `libos_open()` obtains a block capability for the underlying storage and stores it in an internal table indexed by the returned descriptor. System calls like `libos_fork()` communicate with the scheduler using capability-protected endpoints. Memory mapping wrappers allocate pages with `exo_alloc_page()` before installing the mappings.

By layering these wrappers on top of capabilities the system preserves POSIX semantics in user space while retaining the fine grained control of the exokernel.

A small Rust example under `examples/rust` demonstrates the same
capability primitives from a Rust program. Build it using cargo with the
cross-compilation target matching the kernel, for instance:

```sh
rustup target add x86_64-unknown-elf
RUSTFLAGS="-C linker=x86_64-elf-gcc" cargo build --release --target x86_64-unknown-elf
```

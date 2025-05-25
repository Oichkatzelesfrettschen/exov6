# Phoenix POSIX User Guide

This guide explains how to build the Phoenix kernel, compile programs that use the libOS, and how the capability system maps to familiar POSIX interfaces. It supplements the more detailed [phoenixkernel.md](phoenixkernel.md) design notes.

## Building the Kernel and LibOS

Configure a build directory and compile everything with:

```sh
cmake -S . -B build -G Ninja && ninja -C build
```

This produces the kernel image and the user programs. Build the user-space library separately with:

```sh
ninja -C build libos
```

The resulting `libos.a` implements the POSIX wrappers used by applications.

## Compiling Applications

Sources for user programs live under `src-uland/user`. Add the new `*_prog` target to `src-uland/user/CMakeLists.txt` and rebuild. A minimal file reader looks like:

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

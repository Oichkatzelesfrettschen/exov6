# Userland ABI Stability

This document defines the stable interfaces for the Phoenix Userland. Utilities and applications should rely only on these interfaces to ensure compatibility with future kernel and LibOS updates.

## Stable System Calls
The following system calls (defined in `include/syscall.h` and exposed via `user/usys.S`) are considered stable:
- Process: `fork`, `exit`, `wait`, `exec`, `getpid`
- File I/O: `open`, `close`, `read`, `write`, `fstat`, `dup`, `pipe`
- Filesystem: `mkdir`, `chdir`, `link`, `unlink`, `mknod`
- Memory: `sbrk`
- Signals: `kill`
- Time: `sleep`, `uptime`

Utilities should NOT invoke private kernel interfaces (e.g., `SYS_exo_*` unless explicitly required for low-level system management) or rely on undocumented side effects.

## Libc Interfaces
The following libc components (provided by `phoenix-ulib`, `phoenix-printf`, `phoenix-umalloc`) are stable:
- `printf`, `sprintf`
- `malloc`, `free`
- `open`, `read`, `write`, `close` (wrappers)
- `opendir`, `readdir`, `closedir` (newly added directory abstractions)
- String manipulation: `strcmp`, `strcpy`, `strlen`, `memset`, `memmove`

## Directory Access
Direct usage of `read()` on directory file descriptors is deprecated. Utilities must use `opendir()`, `readdir()`, and `closedir()` from `<dirent.h>` to iterate over directories. This abstracts the underlying kernel directory format.

## ABI Versioning
Currently, the ABI is version 1 (v1). Future changes that break binary compatibility will be handled by:
1. Introducing new system calls for new behavior.
2. Versioning libc shared objects (if/when dynamic linking is supported).

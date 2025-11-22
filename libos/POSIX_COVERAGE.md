# POSIX Coverage Matrix

This document tracks the status of POSIX compliance in the Phoenix Exokernel LibOS.

**Compliance Level:**
*   **Implemented**: Fully implemented in LibOS using exokernel primitives.
*   **Partial**: Partially implemented or missing features.
*   **Host Wrapper**: Wrapper around host (Linux) system calls (for testing/development).
*   **Stub**: Returns error or successful no-op.
*   **Missing**: Not present in `libos`.

| Function | Status | Location | Notes |
| :--- | :--- | :--- | :--- |
| **Process Management** | | | |
| `fork` | Host Wrapper | `libos/posix/posix.c` | Calls host `fork()`. Real implementation in `libos/process.c` (WIP). |
| `execve` | Host Wrapper | `libos/posix/posix.c` | Calls host `exec()` via wrapper. |
| `waitpid` | Host Wrapper | `libos/posix/posix.c` | Calls host `wait()`. |
| `exit` | Host Wrapper | `libos/posix/posix.c` | Implicitly used. |
| `getpid` | Host Wrapper | `libos/posix/posix.c` | Calls host `getpid()`. |
| `getpgrp` | Host Wrapper | `libos/posix/posix.c` | Calls host `getpgrp()`. |
| `setpgid` | Host Wrapper | `libos/posix/posix.c` | Calls host `setpgid()`. |
| **File I/O** | | | |
| `open` | Stub / Host Fallback | `libos/posix/posix.c`, `libos/libfs_stubs.c` | Uses `libfs_open` (stub) but falls back to host `open` for invalid FDs. |
| `read` | Stub / Host Fallback | `libos/posix/posix.c` | Uses `libfs_read` (stub) or host `read`. |
| `write` | Stub / Host Fallback | `libos/posix/posix.c` | Uses `libfs_write` (stub) or host `write`. |
| `close` | Stub / Host Fallback | `libos/posix/posix.c` | Uses `libfs_close` (stub) or host `close`. |
| `lseek` | Stub | `libos/posix/posix.c` | Tracks offset in `struct file`, but underlying FS is stubbed. |
| `dup` | Partial | `libos/posix/posix.c` | Implemented for LibOS FD table. |
| `pipe` | Host Wrapper | `libos/posix/posix.c` | Calls host `pipe()`. |
| `stat` | Stub | `libos/posix/posix.c` | Calls `filestat` (stub). |
| `ftruncate` | Stub | `libos/posix/posix.c` | Calls `libfs_truncate` (stub). |
| `mkdir` | Host Wrapper | `libos/posix/posix.c` | Calls host `mkdir()`. |
| `rmdir` | Host Wrapper | `libos/posix/posix.c` | Calls host `unlink()`. |
| `unlink` | Stub | `libos/posix/posix.c` | Calls `libfs_unlink` (stub). |
| `rename` | Stub | `libos/posix/posix.c` | Calls `libfs_rename` (stub). |
| `chdir` | Host Wrapper | `libos/posix/posix.c` | Calls host `chdir()`. |
| `getcwd` | Host Wrapper | `libos/posix/posix.c` | Calls host `getcwd()`. |
| **Memory Management** | | | |
| `mmap` | Hybrid | `libos/posix/posix.c` | Uses `malloc` (host/libc) + `exo_alloc_page` (exokernel). |
| `munmap` | Hybrid | `libos/posix/posix.c` | Uses `free` + `exo_unbind_page`. |
| **Signals** | | | |
| `signal` | Partial | `libos/posix/posix.c` | Stores handlers in `sig_handlers` array. |
| `sigaction` | Partial | `libos/posix/posix.c` | Stores handlers. |
| `sigprocmask` | Partial | `libos/posix/posix.c` | Manages local signal mask. |
| `sigsend` | Stub | `libos/posix/posix.c` | Calls `sigsend` (stub). |
| `killpg` | Stub | `libos/posix/posix.c` | Calls `sigsend` (stub). |
| `sigemptyset` etc. | Implemented | `libos/posix/posix.c` | Bit manipulation. |
| **Networking** | | | |
| `socket` | Host Wrapper | `libos/posix/posix.c` | Calls host `socket()`. |
| `bind` | Host Wrapper | `libos/posix/posix.c` | Calls host `bind()`. |
| `listen` | Host Wrapper | `libos/posix/posix.c` | Calls host `listen()`. |
| `accept` | Host Wrapper | `libos/posix/posix.c` | Calls host `accept()`. |
| `connect` | Host Wrapper | `libos/posix/posix.c` | Calls host `connect()`. |
| `send` | Host Wrapper | `libos/posix/posix.c` | Calls host `send()`. |
| `recv` | Host Wrapper | `libos/posix/posix.c` | Calls host `recv()`. |
| **Environment** | | | |
| `setenv` | Missing | `libos/posix/posix.c` | Declared but not implemented? (Host fallback?) |
| `getenv` | Missing | `libos/posix/posix.c` | Declared but not implemented? (Host fallback?) |

**Summary:**
The current `libos/posix` implementation is primarily a wrapper around host system calls, designed for development and testing on a hosted environment (e.g., Linux). The actual exokernel-native implementation (handling page faults, creating processes via capabilities) is partially present in `libos/process.c` (Process Management) and `libos/libfs_stubs.c` (Filesystem stubs), but is not fully integrated or active.

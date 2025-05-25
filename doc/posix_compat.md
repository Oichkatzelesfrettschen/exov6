# POSIX Compatibility Layer

Phoenix exposes capabilities for blocks, pages and IPC endpoints.
The libOS translates these primitives into familiar POSIX file and
process abstractions.  Each open file stores the underlying block
capability and read/write requests issue disk operations on that block.
Process creation uses capability protected channels to the scheduler but
returns a traditional PID.  Networking calls are thin wrappers around
the host socket APIs.

## Implemented Interfaces
| Interface | Notes |
|-----------|----------------------------------------------|
| `libos_stat` | Returns dummy metadata from the virtual FS. |
| `libos_lseek` | Adjusts the in-memory file offset. |
| `libos_ftruncate` | Ignored by the demo filesystem but provided for compatibility. |
| `libos_mmap` / `libos_munmap` | Allocate and free memory using `malloc`. |
| Signal set operations | `libos_sig*set()` manipulate a bitmask type. |
| Process groups | Forward to the host's `getpgrp()` and `setpgid()` calls. |
| Socket APIs | Thin wrappers around standard Berkeley sockets. |
| `libos_link`/`libos_unlink` | Hard link helpers backed by the xv6 calls. |
| `libos_symlink`/`libos_readlink` | Stubbed out; return `-1` on use. |
| `libos_getcwd`/`libos_chdir` | Report and change the fixed current directory. |
| `libos_execve_env` | `exec` variant that accepts an environment list. |
| `libos_wait` | Wrapper for `wait()` returning any exited child. |


These wrappers mirror the POSIX names where possible but are not fully
featured.  They exist so portability layers can build against Phoenix
without pulling in a real C library.

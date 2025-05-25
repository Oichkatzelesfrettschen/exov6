# POSIX Compatibility Layer

This repository contains a small POSIX wrapper used by the user level
programs.  The implementation is intentionally tiny and only supports a
subset of the standard.  The new helpers added by this change provide
basic stubs so code depending on common interfaces can compile.

## Implemented Interfaces

| Interface                | Notes                                              |
|--------------------------|----------------------------------------------------|
| `libos_stat`             | Returns dummy metadata from the virtual FS.        |
| `libos_lseek`            | Adjusts the in-memory file offset.                 |
| `libos_mmap` / `libos_munmap` | Allocate and free memory using `malloc`.       |
| Signal set operations    | `libos_sig*set()` manipulate a bitmask type.       |
| Process groups           | `libos_getpgrp` and `libos_setpgid` are stubs.     |
| Socket APIs              | `libos_socket` and friends currently return `-1`.  |

These wrappers mirror the POSIX names where possible but are not fully
featured.  They exist so portability layers can build against Phoenix
without pulling in a real C library.

# POSIX Interface Progress

This log tracks implementation status of the POSIX wrappers provided by the Phoenix libOS.  Mark each interface as **Implemented**, **Stubbed**, or **Missing**.  Update the table whenever a new wrapper is merged.

| Interface | Status | Spec | Source |
|-----------|--------|------|--------|
| `libos_open` | Implemented | N/A | [posix.c](../libos/posix.c) |
| `libos_read` | Implemented | [read](ben-books/susv4-2018/functions/read.html) | [posix.c](../libos/posix.c) |
| `libos_write` | Implemented | [write](ben-books/susv4-2018/utilities/write.html) | [posix.c](../libos/posix.c) |
| `libos_close` | Implemented | N/A | [posix.c](../libos/posix.c) |
| `libos_spawn` | Implemented | N/A | [posix.c](../libos/posix.c) |
| `libos_execve` | Implemented | N/A | [posix.c](../libos/posix.c) |
| `libos_mkdir` | Implemented | [mkdir](ben-books/susv4-2018/utilities/mkdir.html) | [posix.c](../libos/posix.c) |
| `libos_rmdir` | Implemented | [rmdir](ben-books/susv4-2018/utilities/rmdir.html) | [posix.c](../libos/posix.c) |
| `libos_signal` | Implemented | N/A | [posix.c](../libos/posix.c) |
| `libos_dup` | Implemented | N/A | [posix.c](../libos/posix.c) |
| `libos_pipe` | Implemented | N/A | [posix.c](../libos/posix.c) |
| `libos_fork` | Implemented | N/A | [posix.c](../libos/posix.c) |
| `libos_waitpid` | Implemented | N/A | [posix.c](../libos/posix.c) |
| `libos_sigsend` | Implemented | N/A | [posix.c](../libos/posix.c) |
| `libos_sigcheck` | Implemented | N/A | [posix.c](../libos/posix.c) |
| `libos_stat` | Implemented | N/A | [posix.c](../libos/posix.c) |
| `libos_lseek` | Implemented | [lseek](ben-books/susv4-2018/functions/lseek.html) | [posix.c](../libos/posix.c) |
| `libos_ftruncate` | Stubbed | N/A | [posix.c](../libos/posix.c) |
| `libos_mmap` | Implemented | [mmap](ben-books/susv4-2018/functions/mmap.html) | [posix.c](../libos/posix.c) |
| `libos_munmap` | Implemented | N/A | [posix.c](../libos/posix.c) |
| `libos_sigemptyset` | Implemented | N/A | [posix.c](../libos/posix.c) |
| `libos_sigfillset` | Implemented | [sigfillset](ben-books/susv4-2018/functions/sigfillset.html) | [posix.c](../libos/posix.c) |
| `libos_sigaddset` | Implemented | N/A | [posix.c](../libos/posix.c) |
| `libos_sigdelset` | Implemented | N/A | [posix.c](../libos/posix.c) |
| `libos_sigismember` | Implemented | N/A | [posix.c](../libos/posix.c) |
| `libos_getpgrp` | Implemented | N/A | [posix.c](../libos/posix.c) |
| `libos_setpgid` | Implemented | N/A | [posix.c](../libos/posix.c) |
| `libos_socket` | Implemented | N/A | [posix.c](../libos/posix.c) |
| `libos_bind` | Implemented | N/A | [posix.c](../libos/posix.c) |
| `libos_listen` | Implemented | N/A | [posix.c](../libos/posix.c) |
| `libos_accept` | Implemented | N/A | [posix.c](../libos/posix.c) |
| `libos_connect` | Implemented | N/A | [posix.c](../libos/posix.c) |
| `libos_send` | Implemented | N/A | [posix.c](../libos/posix.c) |
| `libos_recv` | Implemented | N/A | [posix.c](../libos/posix.c) |
| `libos_rename` | Implemented | N/A | [posix.c](../libos/posix.c) |
| `libos_unlink` | Implemented | [unlink](ben-books/susv4-2018/utilities/unlink.html) | [posix.c](../libos/posix.c) |
| `libos_chdir` | Implemented | N/A | [posix.c](../libos/posix.c) |
| `libos_getcwd` | Implemented | N/A | [posix.c](../libos/posix.c) |

## Notes

- Environment variables set with `libos_setenv()` are local to the process.
  Child processes launched via `libos_spawn()` start with an empty table and do
  not inherit the parent's values.
- Locale support is only stubbed.  Functions such as `setlocale()` and
  `localeconv()` accept arguments but always behave as if the default "C" locale
  is active.


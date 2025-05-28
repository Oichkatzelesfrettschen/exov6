# POSIX Wrapper Matrix

This table lists every wrapper provided by the Phoenix libOS. "Status" records whether the call is fully implemented, just a stub, or not yet present. The "Spec" column links to the Single UNIX Specification HTML when available. "Source" links point to the implementation files. The "Notes" column briefly describes any deviations or missing features.

| Interface | Status | Spec | Source | Notes |
|-----------|--------|------|--------|-------|
| `libos_open` | Implemented | N/A | [posix.c](../libos/posix.c) | Handles `O_CREAT`, `O_TRUNC` and `O_APPEND`. |
| `libos_read` | Implemented | [read](ben-books/susv4-2018/functions/read.html) | [posix.c](../libos/posix.c) | |
| `libos_write` | Implemented | [write](ben-books/susv4-2018/utilities/write.html) | [posix.c](../libos/posix.c) | |
| `libos_close` | Implemented | N/A | [posix.c](../libos/posix.c) | |
| `libos_spawn` | Implemented | N/A | [posix.c](../libos/posix.c) | simple fork/exec wrapper |
| `libos_execve` | Implemented | N/A | [posix.c](../libos/posix.c) | ignores `envp` |
| `libos_mkdir` | Implemented | [mkdir](ben-books/susv4-2018/utilities/mkdir.html) | [posix.c](../libos/posix.c) | |
| `libos_rmdir` | Implemented | [rmdir](ben-books/susv4-2018/utilities/rmdir.html) | [posix.c](../libos/posix.c) | |
| `libos_signal` | Implemented | N/A | [posix.c](../libos/posix.c) | |
| `libos_dup` | Implemented | N/A | [posix.c](../libos/posix.c) | |
| `libos_pipe` | Implemented | N/A | [posix.c](../libos/posix.c) | |
| `libos_fork` | Implemented | N/A | [posix.c](../libos/posix.c) | |
| `libos_waitpid` | Implemented | N/A | [posix.c](../libos/posix.c) | status always 0 |
| `libos_sigsend` | Implemented | N/A | [posix.c](../libos/posix.c) | |
| `libos_sigcheck` | Implemented | N/A | [posix.c](../libos/posix.c) | calls registered handlers |
| `libos_sigaction` | Implemented | N/A | [posix.c](../libos/posix.c) | ignores mask and flags |
| `libos_sigprocmask` | Implemented | N/A | [posix.c](../libos/posix.c) | simple process mask |
| `libos_killpg` | Implemented | N/A | [posix.c](../libos/posix.c) | forwards to `sigsend` |
| `libos_stat` | Implemented | N/A | [posix.c](../libos/posix.c) | returns dummy metadata |
| `libos_lseek` | Implemented | [lseek](ben-books/susv4-2018/functions/lseek.html) | [posix.c](../libos/posix.c) | updates in-memory offset |
| `libos_ftruncate` | Stubbed | N/A | [posix.c](../libos/posix.c) | size change ignored |
| `libos_mmap` | Implemented | [mmap](ben-books/susv4-2018/functions/mmap.html) | [posix.c](../libos/posix.c) | allocates page capability |
| `libos_munmap` | Implemented | N/A | [posix.c](../libos/posix.c) | unbinds page capability |
| `libos_sigemptyset` | Implemented | N/A | [posix.c](../libos/posix.c) | bitmask operation |
| `libos_sigfillset` | Implemented | [sigfillset](ben-books/susv4-2018/functions/sigfillset.html) | [posix.c](../libos/posix.c) | bitmask operation |
| `libos_sigaddset` | Implemented | N/A | [posix.c](../libos/posix.c) | bitmask operation |
| `libos_sigdelset` | Implemented | N/A | [posix.c](../libos/posix.c) | bitmask operation |
| `libos_sigismember` | Implemented | N/A | [posix.c](../libos/posix.c) | bitmask operation |
| `libos_getpgrp` | Implemented | N/A | [posix.c](../libos/posix.c) | uses host API |
| `libos_setpgid` | Implemented | N/A | [posix.c](../libos/posix.c) | uses host API |
| `libos_socket` | Implemented | N/A | [posix.c](../libos/posix.c) | wrapper around host socket |
| `libos_bind` | Implemented | N/A | [posix.c](../libos/posix.c) | wrapper around host socket |
| `libos_listen` | Implemented | N/A | [posix.c](../libos/posix.c) | wrapper around host socket |
| `libos_accept` | Implemented | N/A | [posix.c](../libos/posix.c) | wrapper around host socket |
| `libos_connect` | Implemented | N/A | [posix.c](../libos/posix.c) | wrapper around host socket |
| `libos_send` | Implemented | N/A | [posix.c](../libos/posix.c) | wrapper around host socket |
| `libos_recv` | Implemented | N/A | [posix.c](../libos/posix.c) | wrapper around host socket |
| `libos_setenv` | Implemented | N/A | [env.c](../libos/env.c) | not inherited across processes |
| `libos_getenv` | Implemented | N/A | [env.c](../libos/env.c) | returns value from table |
| `libos_msgq_send` | Implemented | N/A | [ipc.c](../libos/ipc.c) | wraps `exo_send` |
| `libos_msgq_recv` | Implemented | N/A | [ipc.c](../libos/ipc.c) | wraps `exo_recv` |
| `libos_sem_post` | Implemented | N/A | [ipc.c](../libos/ipc.c) | signal semaphore via send |
| `libos_sem_wait` | Implemented | N/A | [ipc.c](../libos/ipc.c) | wait on semaphore via recv |
| `libos_shm_alloc` | Implemented | N/A | [ipc.c](../libos/ipc.c) | allocate page capability |
| `libos_shm_free` | Implemented | N/A | [ipc.c](../libos/ipc.c) | unbind page capability |
| `libos_rename` | Implemented | N/A | [posix.c](../libos/posix.c) | |
| `libos_unlink` | Implemented | [unlink](ben-books/susv4-2018/utilities/unlink.html) | [posix.c](../libos/posix.c) | |
| `libos_chdir` | Implemented | N/A | [posix.c](../libos/posix.c) | |
| `libos_getcwd` | Implemented | N/A | [posix.c](../libos/posix.c) | |


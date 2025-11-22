# Linux System Call Reference for Phoenix LibOS

This document maps standard Linux x86_64 system calls to their implementation status in Phoenix LibOS.

| Syscall # | Name | Status | LibOS Function |
| :--- | :--- | :--- | :--- |
| 0 | `read` | Partial | `libos_read` |
| 1 | `write` | Partial | `libos_write` |
| 2 | `open` | Partial | `libos_open` |
| 3 | `close` | Partial | `libos_close` |
| 4 | `stat` | Stub | `libos_stat` |
| 5 | `fstat` | Stub | `libos_fstat` |
| 6 | `lstat` | Stub | `libos_lstat` |
| 7 | `poll` | Missing | - |
| 8 | `lseek` | Partial | `libos_lseek` |
| 9 | `mmap` | Hybrid | `libos_mmap` |
| 10 | `mprotect` | Missing | - |
| 11 | `munmap` | Hybrid | `libos_munmap` |
| 12 | `brk` | Missing | - |
| 13 | `rt_sigaction` | Partial | `libos_sigaction` |
| 14 | `rt_sigprocmask` | Partial | `libos_sigprocmask` |
| 15 | `rt_sigreturn` | Missing | - |
| 16 | `ioctl` | Stub | `libos_ioctl` |
| ... | ... | ... | ... |
| 39 | `getpid` | Wrapped | `libos_getpid` |
| 41 | `socket` | Wrapped | `libos_socket` |
| 42 | `connect` | Wrapped | `libos_connect` |
| 43 | `accept` | Wrapped | `libos_accept` |
| 44 | `sendto` | Wrapped | `libos_sendto` |
| 45 | `recvfrom` | Wrapped | `libos_recvfrom` |
| ... | ... | ... | ... |
| 57 | `fork` | Wrapped | `libos_fork` |
| 59 | `execve` | Wrapped | `libos_execve` |
| 60 | `exit` | Wrapped | `libos_exit` |
| 61 | `wait4` | Wrapped | `libos_waitpid` |

## Implementation Strategy

1.  **Dispatcher**: The `linux_syscall_handler` will switch on the `rax` register.
2.  **Argument Mapping**: Arguments in `rdi`, `rsi`, `rdx`, `r10`, `r8`, `r9` will be mapped to C function arguments.
3.  **Return Values**: Returns will be placed in `rax`. Errors will be negative `errno` values.

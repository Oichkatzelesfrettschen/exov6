/**
 * @file linux_syscall.h
 * @brief Complete Linux x86_64 Syscall Definitions
 *
 * Comprehensive Linux syscall numbers and structures for x86_64 ABI.
 * Based on Linux kernel 6.x syscall table.
 *
 * References:
 * - https://github.com/torvalds/linux/blob/master/arch/x86/entry/syscalls/syscall_64.tbl
 * - https://man7.org/linux/man-pages/man2/syscalls.2.html
 * - https://filippo.io/linux-syscall-table/
 */

#ifndef _LIBOS_LINUX_SYSCALL_H_
#define _LIBOS_LINUX_SYSCALL_H_

#include <stdint.h>
#include <stddef.h>

/*
 * ============================================================================
 * Linux x86_64 System Call Numbers
 * ============================================================================
 */

/* I/O System Calls (0-20) */
#define __NR_read               0
#define __NR_write              1
#define __NR_open               2
#define __NR_close              3
#define __NR_stat               4
#define __NR_fstat              5
#define __NR_lstat              6
#define __NR_poll               7
#define __NR_lseek              8
#define __NR_mmap               9
#define __NR_mprotect           10
#define __NR_munmap             11
#define __NR_brk                12
#define __NR_rt_sigaction       13
#define __NR_rt_sigprocmask     14
#define __NR_rt_sigreturn       15
#define __NR_ioctl              16
#define __NR_pread64            17
#define __NR_pwrite64           18
#define __NR_readv              19
#define __NR_writev             20

/* File Operations (21-40) */
#define __NR_access             21
#define __NR_pipe               22
#define __NR_select             23
#define __NR_sched_yield        24
#define __NR_mremap             25
#define __NR_msync              26
#define __NR_mincore            27
#define __NR_madvise            28
#define __NR_shmget             29
#define __NR_shmat              30
#define __NR_shmctl             31
#define __NR_dup                32
#define __NR_dup2               33
#define __NR_pause              34
#define __NR_nanosleep          35
#define __NR_getitimer          36
#define __NR_alarm              37
#define __NR_setitimer          38
#define __NR_getpid             39
#define __NR_sendfile           40

/* Socket System Calls (41-55) */
#define __NR_socket             41
#define __NR_connect            42
#define __NR_accept             43
#define __NR_sendto             44
#define __NR_recvfrom           45
#define __NR_sendmsg            46
#define __NR_recvmsg            47
#define __NR_shutdown           48
#define __NR_bind               49
#define __NR_listen             50
#define __NR_getsockname        51
#define __NR_getpeername        52
#define __NR_socketpair         53
#define __NR_setsockopt         54
#define __NR_getsockopt         55

/* Process Control (56-70) */
#define __NR_clone              56
#define __NR_fork               57
#define __NR_vfork              58
#define __NR_execve             59
#define __NR_exit               60
#define __NR_wait4              61
#define __NR_kill               62
#define __NR_uname              63
#define __NR_semget             64
#define __NR_semop              65
#define __NR_semctl             66
#define __NR_shmdt              67
#define __NR_msgget             68
#define __NR_msgsnd             69
#define __NR_msgrcv             70

/* File Descriptor Operations (71-100) */
#define __NR_msgctl             71
#define __NR_fcntl              72
#define __NR_flock              73
#define __NR_fsync              74
#define __NR_fdatasync          75
#define __NR_truncate           76
#define __NR_ftruncate          77
#define __NR_getdents           78
#define __NR_getcwd             79
#define __NR_chdir              80
#define __NR_fchdir             81
#define __NR_rename             82
#define __NR_mkdir              83
#define __NR_rmdir              84
#define __NR_creat              85
#define __NR_link               86
#define __NR_unlink             87
#define __NR_symlink            88
#define __NR_readlink           89
#define __NR_chmod              90
#define __NR_fchmod             91
#define __NR_chown              92
#define __NR_fchown             93
#define __NR_lchown             94
#define __NR_umask              95
#define __NR_gettimeofday       96
#define __NR_getrlimit          97
#define __NR_getrusage          98
#define __NR_sysinfo            99
#define __NR_times              100

/* Process/Thread Info (101-130) */
#define __NR_ptrace             101
#define __NR_getuid             102
#define __NR_syslog             103
#define __NR_getgid             104
#define __NR_setuid             105
#define __NR_setgid             106
#define __NR_geteuid            107
#define __NR_getegid            108
#define __NR_setpgid            109
#define __NR_getppid            110
#define __NR_getpgrp            111
#define __NR_setsid             112
#define __NR_setreuid           113
#define __NR_setregid           114
#define __NR_getgroups          115
#define __NR_setgroups          116
#define __NR_setresuid          117
#define __NR_getresuid          118
#define __NR_setresgid          119
#define __NR_getresgid          120
#define __NR_getpgid            121
#define __NR_setfsuid           122
#define __NR_setfsgid           123
#define __NR_getsid             124
#define __NR_capget             125
#define __NR_capset             126
#define __NR_rt_sigpending      127
#define __NR_rt_sigtimedwait    128
#define __NR_rt_sigqueueinfo    129
#define __NR_rt_sigsuspend      130

/* Signals & Timers (131-150) */
#define __NR_sigaltstack        131
#define __NR_utime              132
#define __NR_mknod              133
#define __NR_uselib             134
#define __NR_personality        135
#define __NR_ustat              136
#define __NR_statfs             137
#define __NR_fstatfs            138
#define __NR_sysfs              139
#define __NR_getpriority        140
#define __NR_setpriority        141
#define __NR_sched_setparam     142
#define __NR_sched_getparam     143
#define __NR_sched_setscheduler 144
#define __NR_sched_getscheduler 145
#define __NR_sched_get_priority_max 146
#define __NR_sched_get_priority_min 147
#define __NR_sched_rr_get_interval 148
#define __NR_mlock              149
#define __NR_munlock            150

/* Memory & Locking (151-180) */
#define __NR_mlockall           151
#define __NR_munlockall         152
#define __NR_vhangup            153
#define __NR_modify_ldt         154
#define __NR_pivot_root         155
#define __NR__sysctl            156
#define __NR_prctl              157
#define __NR_arch_prctl         158
#define __NR_adjtimex           159
#define __NR_setrlimit          160
#define __NR_chroot             161
#define __NR_sync               162
#define __NR_acct               163
#define __NR_settimeofday       164
#define __NR_mount              165
#define __NR_umount2            166
#define __NR_swapon             167
#define __NR_swapoff            168
#define __NR_reboot             169
#define __NR_sethostname        170
#define __NR_setdomainname      171
#define __NR_iopl               172
#define __NR_ioperm             173
#define __NR_create_module      174
#define __NR_init_module        175
#define __NR_delete_module      176
#define __NR_get_kernel_syms    177
#define __NR_query_module       178
#define __NR_quotactl           179
#define __NR_nfsservctl         180

/* IDs & Quotas (181-210) */
#define __NR_getpmsg            181
#define __NR_putpmsg            182
#define __NR_afs_syscall        183
#define __NR_tuxcall            184
#define __NR_security           185
#define __NR_gettid             186
#define __NR_readahead          187
#define __NR_setxattr           188
#define __NR_lsetxattr          189
#define __NR_fsetxattr          190
#define __NR_getxattr           191
#define __NR_lgetxattr          192
#define __NR_fgetxattr          193
#define __NR_listxattr          194
#define __NR_llistxattr         195
#define __NR_flistxattr         196
#define __NR_removexattr        197
#define __NR_lremovexattr       198
#define __NR_fremovexattr       199
#define __NR_tkill              200
#define __NR_time               201
#define __NR_futex              202
#define __NR_sched_setaffinity  203
#define __NR_sched_getaffinity  204
#define __NR_set_thread_area    205
#define __NR_io_setup           206
#define __NR_io_destroy         207
#define __NR_io_getevents       208
#define __NR_io_submit          209
#define __NR_io_cancel          210

/* Event & Timer FDs (211-240) */
#define __NR_get_thread_area    211
#define __NR_lookup_dcookie     212
#define __NR_epoll_create       213
#define __NR_epoll_ctl_old      214
#define __NR_epoll_wait_old     215
#define __NR_remap_file_pages   216
#define __NR_getdents64         217
#define __NR_set_tid_address    218
#define __NR_restart_syscall    219
#define __NR_semtimedop         220
#define __NR_fadvise64          221
#define __NR_timer_create       222
#define __NR_timer_settime      223
#define __NR_timer_gettime      224
#define __NR_timer_getoverrun   225
#define __NR_timer_delete       226
#define __NR_clock_settime      227
#define __NR_clock_gettime      228
#define __NR_clock_getres       229
#define __NR_clock_nanosleep    230
#define __NR_exit_group         231
#define __NR_epoll_wait         232
#define __NR_epoll_ctl          233
#define __NR_tgkill             234
#define __NR_utimes             235
#define __NR_vserver            236
#define __NR_mbind              237
#define __NR_set_mempolicy      238
#define __NR_get_mempolicy      239
#define __NR_mq_open            240

/* Message Queues & Keys (241-270) */
#define __NR_mq_unlink          241
#define __NR_mq_timedsend       242
#define __NR_mq_timedreceive    243
#define __NR_mq_notify          244
#define __NR_mq_getsetattr      245
#define __NR_kexec_load         246
#define __NR_waitid             247
#define __NR_add_key            248
#define __NR_request_key        249
#define __NR_keyctl             250
#define __NR_ioprio_set         251
#define __NR_ioprio_get         252
#define __NR_inotify_init       253
#define __NR_inotify_add_watch  254
#define __NR_inotify_rm_watch   255
#define __NR_migrate_pages      256
#define __NR_openat             257
#define __NR_mkdirat            258
#define __NR_mknodat            259
#define __NR_fchownat           260
#define __NR_futimesat          261
#define __NR_newfstatat         262
#define __NR_unlinkat           263
#define __NR_renameat           264
#define __NR_linkat             265
#define __NR_symlinkat          266
#define __NR_readlinkat         267
#define __NR_fchmodat           268
#define __NR_faccessat          269
#define __NR_pselect6           270

/* Modern Syscalls (271-330) */
#define __NR_ppoll              271
#define __NR_unshare            272
#define __NR_set_robust_list    273
#define __NR_get_robust_list    274
#define __NR_splice             275
#define __NR_tee                276
#define __NR_sync_file_range    277
#define __NR_vmsplice           278
#define __NR_move_pages         279
#define __NR_utimensat          280
#define __NR_epoll_pwait        281
#define __NR_signalfd           282
#define __NR_timerfd_create     283
#define __NR_eventfd            284
#define __NR_fallocate          285
#define __NR_timerfd_settime    286
#define __NR_timerfd_gettime    287
#define __NR_accept4            288
#define __NR_signalfd4          289
#define __NR_eventfd2           290
#define __NR_epoll_create1      291
#define __NR_dup3               292
#define __NR_pipe2              293
#define __NR_inotify_init1      294
#define __NR_preadv             295
#define __NR_pwritev            296
#define __NR_rt_tgsigqueueinfo  297
#define __NR_perf_event_open    298
#define __NR_recvmmsg           299
#define __NR_fanotify_init      300
#define __NR_fanotify_mark      301
#define __NR_prlimit64          302
#define __NR_name_to_handle_at  303
#define __NR_open_by_handle_at  304
#define __NR_clock_adjtime      305
#define __NR_syncfs             306
#define __NR_sendmmsg           307
#define __NR_setns              308
#define __NR_getcpu             309
#define __NR_process_vm_readv   310
#define __NR_process_vm_writev  311
#define __NR_kcmp               312
#define __NR_finit_module       313
#define __NR_sched_setattr      314
#define __NR_sched_getattr      315
#define __NR_renameat2          316
#define __NR_seccomp            317
#define __NR_getrandom          318
#define __NR_memfd_create       319
#define __NR_kexec_file_load    320
#define __NR_bpf                321
#define __NR_execveat           322
#define __NR_userfaultfd        323
#define __NR_membarrier         324
#define __NR_mlock2             325
#define __NR_copy_file_range    326
#define __NR_preadv2            327
#define __NR_pwritev2           328
#define __NR_pkey_mprotect      329
#define __NR_pkey_alloc         330

/* Newest Syscalls (331-450) */
#define __NR_pkey_free          331
#define __NR_statx              332
#define __NR_io_pgetevents      333
#define __NR_rseq               334
#define __NR_pidfd_send_signal  424
#define __NR_io_uring_setup     425
#define __NR_io_uring_enter     426
#define __NR_io_uring_register  427
#define __NR_open_tree          428
#define __NR_move_mount         429
#define __NR_fsopen             430
#define __NR_fsconfig           431
#define __NR_fsmount            432
#define __NR_fspick             433
#define __NR_pidfd_open         434
#define __NR_clone3             435
#define __NR_close_range        436
#define __NR_openat2            437
#define __NR_pidfd_getfd        438
#define __NR_faccessat2         439
#define __NR_process_madvise    440
#define __NR_epoll_pwait2       441
#define __NR_mount_setattr      442
#define __NR_quotactl_fd        443
#define __NR_landlock_create_ruleset 444
#define __NR_landlock_add_rule  445
#define __NR_landlock_restrict_self 446
#define __NR_memfd_secret       447
#define __NR_process_mrelease   448
#define __NR_futex_waitv        449
#define __NR_set_mempolicy_home_node 450

/*
 * ============================================================================
 * Clone Flags (for clone/clone3 syscall)
 * ============================================================================
 */

#define CLONE_VM                0x00000100  /* Share virtual memory */
#define CLONE_FS                0x00000200  /* Share filesystem info */
#define CLONE_FILES             0x00000400  /* Share file descriptors */
#define CLONE_SIGHAND           0x00000800  /* Share signal handlers */
#define CLONE_PIDFD             0x00001000  /* Create pidfd */
#define CLONE_PTRACE            0x00002000  /* Allow ptrace by parent */
#define CLONE_VFORK             0x00004000  /* Parent sleeps until child calls execve/exit */
#define CLONE_PARENT            0x00008000  /* Same parent as cloner */
#define CLONE_THREAD            0x00010000  /* Same thread group */
#define CLONE_NEWNS             0x00020000  /* New mount namespace */
#define CLONE_SYSVSEM           0x00040000  /* Share SysV SEM_UNDO */
#define CLONE_SETTLS            0x00080000  /* Set TLS descriptor */
#define CLONE_PARENT_SETTID     0x00100000  /* Set TID in parent */
#define CLONE_CHILD_CLEARTID    0x00200000  /* Clear TID in child */
#define CLONE_DETACHED          0x00400000  /* Unused */
#define CLONE_UNTRACED          0x00800000  /* No ptrace */
#define CLONE_CHILD_SETTID      0x01000000  /* Set TID in child */
#define CLONE_NEWCGROUP         0x02000000  /* New cgroup namespace */
#define CLONE_NEWUTS            0x04000000  /* New UTS namespace */
#define CLONE_NEWIPC            0x08000000  /* New IPC namespace */
#define CLONE_NEWUSER           0x10000000  /* New user namespace */
#define CLONE_NEWPID            0x20000000  /* New PID namespace */
#define CLONE_NEWNET            0x40000000  /* New network namespace */
#define CLONE_IO                0x80000000  /* Clone I/O context */

/*
 * ============================================================================
 * Futex Operations
 * ============================================================================
 */

#define FUTEX_WAIT              0
#define FUTEX_WAKE              1
#define FUTEX_FD                2   /* Deprecated */
#define FUTEX_REQUEUE           3
#define FUTEX_CMP_REQUEUE       4
#define FUTEX_WAKE_OP           5
#define FUTEX_LOCK_PI           6
#define FUTEX_UNLOCK_PI         7
#define FUTEX_TRYLOCK_PI        8
#define FUTEX_WAIT_BITSET       9
#define FUTEX_WAKE_BITSET       10
#define FUTEX_WAIT_REQUEUE_PI   11
#define FUTEX_CMP_REQUEUE_PI    12

/* Futex flags */
#define FUTEX_PRIVATE_FLAG      128
#define FUTEX_CLOCK_REALTIME    256

#define FUTEX_WAIT_PRIVATE      (FUTEX_WAIT | FUTEX_PRIVATE_FLAG)
#define FUTEX_WAKE_PRIVATE      (FUTEX_WAKE | FUTEX_PRIVATE_FLAG)

#define FUTEX_BITSET_MATCH_ANY  0xffffffff

/*
 * ============================================================================
 * Epoll Constants
 * ============================================================================
 */

/* epoll_create1 flags */
#define EPOLL_CLOEXEC           0x80000

/* epoll_ctl operations */
#define EPOLL_CTL_ADD           1
#define EPOLL_CTL_DEL           2
#define EPOLL_CTL_MOD           3

/* epoll events */
#define EPOLLIN                 0x001
#define EPOLLPRI                0x002
#define EPOLLOUT                0x004
#define EPOLLERR                0x008
#define EPOLLHUP                0x010
#define EPOLLRDNORM             0x040
#define EPOLLRDBAND             0x080
#define EPOLLWRNORM             0x100
#define EPOLLWRBAND             0x200
#define EPOLLMSG                0x400
#define EPOLLRDHUP              0x2000
#define EPOLLEXCLUSIVE          (1U << 28)
#define EPOLLWAKEUP             (1U << 29)
#define EPOLLONESHOT            (1U << 30)
#define EPOLLET                 (1U << 31)

/*
 * ============================================================================
 * Signal Constants
 * ============================================================================
 */

#define LINUX_SIGHUP            1
#define LINUX_SIGINT            2
#define LINUX_SIGQUIT           3
#define LINUX_SIGILL            4
#define LINUX_SIGTRAP           5
#define LINUX_SIGABRT           6
#define LINUX_SIGBUS            7
#define LINUX_SIGFPE            8
#define LINUX_SIGKILL           9
#define LINUX_SIGUSR1           10
#define LINUX_SIGSEGV           11
#define LINUX_SIGUSR2           12
#define LINUX_SIGPIPE           13
#define LINUX_SIGALRM           14
#define LINUX_SIGTERM           15
#define LINUX_SIGSTKFLT         16
#define LINUX_SIGCHLD           17
#define LINUX_SIGCONT           18
#define LINUX_SIGSTOP           19
#define LINUX_SIGTSTP           20
#define LINUX_SIGTTIN           21
#define LINUX_SIGTTOU           22
#define LINUX_SIGURG            23
#define LINUX_SIGXCPU           24
#define LINUX_SIGXFSZ           25
#define LINUX_SIGVTALRM         26
#define LINUX_SIGPROF           27
#define LINUX_SIGWINCH          28
#define LINUX_SIGIO             29
#define LINUX_SIGPWR            30
#define LINUX_SIGSYS            31
#define LINUX_SIGRTMIN          32
#define LINUX_SIGRTMAX          64

#define LINUX_NSIG              64

/* Signal action flags */
#define LINUX_SA_NOCLDSTOP      0x00000001
#define LINUX_SA_NOCLDWAIT      0x00000002
#define LINUX_SA_SIGINFO        0x00000004
#define LINUX_SA_ONSTACK        0x08000000
#define LINUX_SA_RESTART        0x10000000
#define LINUX_SA_NODEFER        0x40000000
#define LINUX_SA_RESETHAND      0x80000000
#define LINUX_SA_RESTORER       0x04000000

/*
 * ============================================================================
 * Memory Protection Flags
 * ============================================================================
 */

#define LINUX_PROT_NONE         0x0
#define LINUX_PROT_READ         0x1
#define LINUX_PROT_WRITE        0x2
#define LINUX_PROT_EXEC         0x4
#define LINUX_PROT_GROWSDOWN    0x01000000
#define LINUX_PROT_GROWSUP      0x02000000

/* mmap flags */
#define LINUX_MAP_SHARED        0x01
#define LINUX_MAP_PRIVATE       0x02
#define LINUX_MAP_FIXED         0x10
#define LINUX_MAP_ANONYMOUS     0x20
#define LINUX_MAP_GROWSDOWN     0x0100
#define LINUX_MAP_DENYWRITE     0x0800
#define LINUX_MAP_EXECUTABLE    0x1000
#define LINUX_MAP_LOCKED        0x2000
#define LINUX_MAP_NORESERVE     0x4000
#define LINUX_MAP_POPULATE      0x8000
#define LINUX_MAP_NONBLOCK      0x10000
#define LINUX_MAP_STACK         0x20000
#define LINUX_MAP_HUGETLB       0x40000
#define LINUX_MAP_SYNC          0x80000
#define LINUX_MAP_FIXED_NOREPLACE 0x100000

/*
 * ============================================================================
 * File Descriptor Flags
 * ============================================================================
 */

#define LINUX_O_RDONLY          0x0000
#define LINUX_O_WRONLY          0x0001
#define LINUX_O_RDWR            0x0002
#define LINUX_O_CREAT           0x0040
#define LINUX_O_EXCL            0x0080
#define LINUX_O_NOCTTY          0x0100
#define LINUX_O_TRUNC           0x0200
#define LINUX_O_APPEND          0x0400
#define LINUX_O_NONBLOCK        0x0800
#define LINUX_O_DSYNC           0x1000
#define LINUX_O_ASYNC           0x2000
#define LINUX_O_DIRECT          0x4000
#define LINUX_O_LARGEFILE       0x8000
#define LINUX_O_DIRECTORY       0x10000
#define LINUX_O_NOFOLLOW        0x20000
#define LINUX_O_NOATIME         0x40000
#define LINUX_O_CLOEXEC         0x80000
#define LINUX_O_PATH            0x200000
#define LINUX_O_TMPFILE         0x400000

/* AT_* constants for *at() syscalls */
#define LINUX_AT_FDCWD          -100
#define LINUX_AT_SYMLINK_NOFOLLOW 0x100
#define LINUX_AT_REMOVEDIR      0x200
#define LINUX_AT_SYMLINK_FOLLOW 0x400
#define LINUX_AT_NO_AUTOMOUNT   0x800
#define LINUX_AT_EMPTY_PATH     0x1000
#define LINUX_AT_EACCESS        0x200

/* O_ACCMODE and settable flags */
#define LINUX_O_ACCMODE         0x0003
#define LINUX_O_SETFL_MASK      (LINUX_O_APPEND | LINUX_O_ASYNC | LINUX_O_DIRECT | \
                                 LINUX_O_NOATIME | LINUX_O_NONBLOCK)

/* File descriptor constants */
#define LINUX_OPEN_MAX          1024
#define LINUX_IOV_MAX           1024
#define LINUX_FD_CLOEXEC        1

/*
 * ============================================================================
 * Linux Error Numbers
 * ============================================================================
 */

#define LINUX_EPERM             1
#define LINUX_ENOENT            2
#define LINUX_ESRCH             3
#define LINUX_EINTR             4
#define LINUX_EIO               5
#define LINUX_ENXIO             6
#define LINUX_E2BIG             7
#define LINUX_ENOEXEC           8
#define LINUX_EBADF             9
#define LINUX_ECHILD            10
#define LINUX_EAGAIN            11
#define LINUX_ENOMEM            12
#define LINUX_EACCES            13
#define LINUX_EFAULT            14
#define LINUX_ENOTBLK           15
#define LINUX_EBUSY             16
#define LINUX_EEXIST            17
#define LINUX_EXDEV             18
#define LINUX_ENODEV            19
#define LINUX_ENOTDIR           20
#define LINUX_EISDIR            21
#define LINUX_EINVAL            22
#define LINUX_ENFILE            23
#define LINUX_EMFILE            24
#define LINUX_ENOTTY            25
#define LINUX_ETXTBSY           26
#define LINUX_EFBIG             27
#define LINUX_ENOSPC            28
#define LINUX_ESPIPE            29
#define LINUX_EROFS             30
#define LINUX_EMLINK            31
#define LINUX_EPIPE             32
#define LINUX_EDOM              33
#define LINUX_ERANGE            34
#define LINUX_EDEADLK           35
#define LINUX_ENAMETOOLONG      36
#define LINUX_ENOLCK            37
#define LINUX_ENOSYS            38
#define LINUX_ENOTEMPTY         39
#define LINUX_ELOOP             40
#define LINUX_EWOULDBLOCK       LINUX_EAGAIN
#define LINUX_ENOMSG            42
#define LINUX_EIDRM             43
#define LINUX_ETIMEDOUT         110

/*
 * ============================================================================
 * Signal Mask Operations
 * ============================================================================
 */

#define LINUX_SIG_BLOCK         0
#define LINUX_SIG_UNBLOCK       1
#define LINUX_SIG_SETMASK       2

/* Signal stack flags */
#define LINUX_SS_ONSTACK        1
#define LINUX_SS_DISABLE        2
#define LINUX_MINSIGSTKSZ       2048
#define LINUX_SIGSTKSZ          8192

/*
 * ============================================================================
 * madvise Hints
 * ============================================================================
 */

#define LINUX_MADV_NORMAL       0
#define LINUX_MADV_RANDOM       1
#define LINUX_MADV_SEQUENTIAL   2
#define LINUX_MADV_WILLNEED     3
#define LINUX_MADV_DONTNEED     4
#define LINUX_MADV_FREE         8
#define LINUX_MADV_REMOVE       9
#define LINUX_MADV_DONTFORK     10
#define LINUX_MADV_DOFORK       11
#define LINUX_MADV_MERGEABLE    12
#define LINUX_MADV_UNMERGEABLE  13
#define LINUX_MADV_HUGEPAGE     14
#define LINUX_MADV_NOHUGEPAGE   15
#define LINUX_MADV_DONTDUMP     16
#define LINUX_MADV_DODUMP       17

/*
 * ============================================================================
 * mlock Flags
 * ============================================================================
 */

#define LINUX_MCL_CURRENT       1
#define LINUX_MCL_FUTURE        2
#define LINUX_MCL_ONFAULT       4
#define LINUX_MLOCK_ONFAULT     1

/*
 * ============================================================================
 * mremap Flags
 * ============================================================================
 */

#define LINUX_MREMAP_MAYMOVE    1
#define LINUX_MREMAP_FIXED      2
#define LINUX_MREMAP_DONTUNMAP  4

/*
 * ============================================================================
 * fcntl Commands
 * ============================================================================
 */

#define LINUX_F_DUPFD           0
#define LINUX_F_GETFD           1
#define LINUX_F_SETFD           2
#define LINUX_F_GETFL           3
#define LINUX_F_SETFL           4
#define LINUX_F_GETLK           5
#define LINUX_F_SETLK           6
#define LINUX_F_SETLKW          7
#define LINUX_F_SETOWN          8
#define LINUX_F_GETOWN          9
#define LINUX_F_DUPFD_CLOEXEC   1030

/*
 * ============================================================================
 * ioctl Requests
 * ============================================================================
 */

#define LINUX_FIONREAD          0x541B
#define LINUX_FIONBIO           0x5421
#define LINUX_FIOCLEX           0x5451
#define LINUX_FIONCLEX          0x5450

/*
 * ============================================================================
 * prctl Operations
 * ============================================================================
 */

#define PR_SET_PDEATHSIG        1
#define PR_GET_PDEATHSIG        2
#define PR_GET_DUMPABLE         3
#define PR_SET_DUMPABLE         4
#define PR_GET_UNALIGN          5
#define PR_SET_UNALIGN          6
#define PR_GET_KEEPCAPS         7
#define PR_SET_KEEPCAPS         8
#define PR_GET_FPEMU            9
#define PR_SET_FPEMU            10
#define PR_GET_FPEXC            11
#define PR_SET_FPEXC            12
#define PR_GET_TIMING           13
#define PR_SET_TIMING           14
#define PR_SET_NAME             15
#define PR_GET_NAME             16
#define PR_GET_SECCOMP          21
#define PR_SET_SECCOMP          22
#define PR_GET_TSC              25
#define PR_SET_TSC              26
#define PR_GET_NO_NEW_PRIVS     39
#define PR_SET_NO_NEW_PRIVS     38

/*
 * ============================================================================
 * Linux Structures
 * ============================================================================
 */

/* stat structure (x86_64) */
struct linux_stat {
    uint64_t    st_dev;
    uint64_t    st_ino;
    uint64_t    st_nlink;
    uint32_t    st_mode;
    uint32_t    st_uid;
    uint32_t    st_gid;
    uint32_t    __pad0;
    uint64_t    st_rdev;
    int64_t     st_size;
    int64_t     st_blksize;
    int64_t     st_blocks;
    uint64_t    st_atime;
    uint64_t    st_atime_nsec;
    uint64_t    st_mtime;
    uint64_t    st_mtime_nsec;
    uint64_t    st_ctime;
    uint64_t    st_ctime_nsec;
    int64_t     __unused[3];
};

/* statx structure (newer) */
struct linux_statx_timestamp {
    int64_t     tv_sec;
    uint32_t    tv_nsec;
    int32_t     __reserved;
};

struct linux_statx {
    uint32_t    stx_mask;
    uint32_t    stx_blksize;
    uint64_t    stx_attributes;
    uint32_t    stx_nlink;
    uint32_t    stx_uid;
    uint32_t    stx_gid;
    uint16_t    stx_mode;
    uint16_t    __spare0[1];
    uint64_t    stx_ino;
    uint64_t    stx_size;
    uint64_t    stx_blocks;
    uint64_t    stx_attributes_mask;
    struct linux_statx_timestamp stx_atime;
    struct linux_statx_timestamp stx_btime;
    struct linux_statx_timestamp stx_ctime;
    struct linux_statx_timestamp stx_mtime;
    uint32_t    stx_rdev_major;
    uint32_t    stx_rdev_minor;
    uint32_t    stx_dev_major;
    uint32_t    stx_dev_minor;
    uint64_t    stx_mnt_id;
    uint64_t    __spare2;
    uint64_t    __spare3[12];
};

/* epoll_event structure */
struct linux_epoll_event {
    uint32_t    events;
    uint64_t    data;
} __attribute__((packed));

/* sigaction structure */
struct linux_sigaction {
    void        (*sa_handler)(int);
    unsigned long sa_flags;
    void        (*sa_restorer)(void);
    uint64_t    sa_mask;
};

/* timespec structure */
struct linux_timespec {
    int64_t     tv_sec;
    int64_t     tv_nsec;
};

/* timeval structure */
struct linux_timeval {
    int64_t     tv_sec;
    int64_t     tv_usec;
};

/* iovec structure */
struct linux_iovec {
    void       *iov_base;
    size_t      iov_len;
};

/* utsname structure */
struct linux_utsname {
    char sysname[65];
    char nodename[65];
    char release[65];
    char version[65];
    char machine[65];
    char domainname[65];
};

/* rlimit structure */
struct linux_rlimit {
    uint64_t    rlim_cur;
    uint64_t    rlim_max;
};

/* rusage structure */
struct linux_rusage {
    struct linux_timeval ru_utime;
    struct linux_timeval ru_stime;
    long ru_maxrss;
    long ru_ixrss;
    long ru_idrss;
    long ru_isrss;
    long ru_minflt;
    long ru_majflt;
    long ru_nswap;
    long ru_inblock;
    long ru_oublock;
    long ru_msgsnd;
    long ru_msgrcv;
    long ru_nsignals;
    long ru_nvcsw;
    long ru_nivcsw;
};

/* clone_args for clone3 */
struct linux_clone_args {
    uint64_t    flags;
    uint64_t    pidfd;
    uint64_t    child_tid;
    uint64_t    parent_tid;
    uint64_t    exit_signal;
    uint64_t    stack;
    uint64_t    stack_size;
    uint64_t    tls;
    uint64_t    set_tid;
    uint64_t    set_tid_size;
    uint64_t    cgroup;
};

/* sysinfo structure */
struct linux_sysinfo {
    long uptime;
    unsigned long loads[3];
    unsigned long totalram;
    unsigned long freeram;
    unsigned long sharedram;
    unsigned long bufferram;
    unsigned long totalswap;
    unsigned long freeswap;
    unsigned short procs;
    unsigned short pad;
    unsigned long totalhigh;
    unsigned long freehigh;
    unsigned int mem_unit;
    char _f[20 - 2 * sizeof(long) - sizeof(int)];
};

/* Directory entry */
struct linux_dirent64 {
    uint64_t    d_ino;
    int64_t     d_off;
    uint16_t    d_reclen;
    uint8_t     d_type;
    char        d_name[];
};

/* Robust futex list */
struct linux_robust_list {
    struct linux_robust_list *next;
};

struct linux_robust_list_head {
    struct linux_robust_list list;
    long futex_offset;
    struct linux_robust_list *list_op_pending;
};

#endif /* _LIBOS_LINUX_SYSCALL_H_ */

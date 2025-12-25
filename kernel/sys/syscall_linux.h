/**
 * @file syscall_linux.h
 * @brief Linux syscall compatibility layer
 * 
 * Provides Linux syscall numbers and structures for binary compatibility.
 * Based on Linux 6.x x86_64 ABI.
 */

#pragma once

#include <stdint.h>
#include <stddef.h>
#include "syscall_gateway.h"

// =============================================================================
// LINUX x86_64 SYSCALL NUMBERS
// =============================================================================

// Core I/O syscalls
#define LINUX_SYS_read              0
#define LINUX_SYS_write             1
#define LINUX_SYS_open              2
#define LINUX_SYS_close             3
#define LINUX_SYS_stat              4
#define LINUX_SYS_fstat             5
#define LINUX_SYS_lstat             6
#define LINUX_SYS_poll              7
#define LINUX_SYS_lseek             8
#define LINUX_SYS_mmap              9
#define LINUX_SYS_mprotect          10
#define LINUX_SYS_munmap            11
#define LINUX_SYS_brk               12
#define LINUX_SYS_rt_sigaction      13
#define LINUX_SYS_rt_sigprocmask    14
#define LINUX_SYS_rt_sigreturn      15
#define LINUX_SYS_ioctl             16
#define LINUX_SYS_pread64           17
#define LINUX_SYS_pwrite64          18
#define LINUX_SYS_readv             19
#define LINUX_SYS_writev            20
#define LINUX_SYS_access            21
#define LINUX_SYS_pipe              22
#define LINUX_SYS_select            23
#define LINUX_SYS_sched_yield       24
#define LINUX_SYS_mremap            25
#define LINUX_SYS_msync             26
#define LINUX_SYS_mincore           27
#define LINUX_SYS_madvise           28
#define LINUX_SYS_shmget            29
#define LINUX_SYS_shmat             30
#define LINUX_SYS_shmctl            31
#define LINUX_SYS_dup               32
#define LINUX_SYS_dup2              33
#define LINUX_SYS_pause             34
#define LINUX_SYS_nanosleep         35
#define LINUX_SYS_getitimer         36
#define LINUX_SYS_alarm             37
#define LINUX_SYS_setitimer         38
#define LINUX_SYS_getpid            39
#define LINUX_SYS_sendfile          40
#define LINUX_SYS_socket            41
#define LINUX_SYS_connect           42
#define LINUX_SYS_accept            43
#define LINUX_SYS_sendto            44
#define LINUX_SYS_recvfrom          45
#define LINUX_SYS_sendmsg           46
#define LINUX_SYS_recvmsg           47
#define LINUX_SYS_shutdown          48
#define LINUX_SYS_bind              49
#define LINUX_SYS_listen            50
#define LINUX_SYS_getsockname       51
#define LINUX_SYS_getpeername       52
#define LINUX_SYS_socketpair        53
#define LINUX_SYS_setsockopt        54
#define LINUX_SYS_getsockopt        55
#define LINUX_SYS_clone             56
#define LINUX_SYS_fork              57
#define LINUX_SYS_vfork             58
#define LINUX_SYS_execve            59
#define LINUX_SYS_exit              60
#define LINUX_SYS_wait4             61
#define LINUX_SYS_kill              62
#define LINUX_SYS_uname             63
#define LINUX_SYS_semget            64
#define LINUX_SYS_semop             65
#define LINUX_SYS_semctl            66
#define LINUX_SYS_shmdt             67
#define LINUX_SYS_msgget            68
#define LINUX_SYS_msgsnd            69
#define LINUX_SYS_msgrcv            70
#define LINUX_SYS_msgctl            71
#define LINUX_SYS_fcntl             72
#define LINUX_SYS_flock             73
#define LINUX_SYS_fsync             74
#define LINUX_SYS_fdatasync         75
#define LINUX_SYS_truncate          76
#define LINUX_SYS_ftruncate         77
#define LINUX_SYS_getdents          78
#define LINUX_SYS_getcwd            79
#define LINUX_SYS_chdir             80
#define LINUX_SYS_fchdir            81
#define LINUX_SYS_rename            82
#define LINUX_SYS_mkdir             83
#define LINUX_SYS_rmdir             84
#define LINUX_SYS_creat             85
#define LINUX_SYS_link              86
#define LINUX_SYS_unlink            87
#define LINUX_SYS_symlink           88
#define LINUX_SYS_readlink          89
#define LINUX_SYS_chmod             90
#define LINUX_SYS_fchmod            91
#define LINUX_SYS_chown             92
#define LINUX_SYS_fchown            93
#define LINUX_SYS_lchown            94
#define LINUX_SYS_umask             95
#define LINUX_SYS_gettimeofday      96
#define LINUX_SYS_getrlimit         97
#define LINUX_SYS_getrusage         98
#define LINUX_SYS_sysinfo           99
#define LINUX_SYS_times             100
#define LINUX_SYS_ptrace            101
#define LINUX_SYS_getuid            102
#define LINUX_SYS_syslog            103
#define LINUX_SYS_getgid            104
#define LINUX_SYS_setuid            105
#define LINUX_SYS_setgid            106
#define LINUX_SYS_geteuid           107
#define LINUX_SYS_getegid           108
#define LINUX_SYS_setpgid           109
#define LINUX_SYS_getppid           110
#define LINUX_SYS_getpgrp           111
#define LINUX_SYS_setsid            112
#define LINUX_SYS_setreuid          113
#define LINUX_SYS_setregid          114
#define LINUX_SYS_getgroups         115
#define LINUX_SYS_setgroups         116
#define LINUX_SYS_setresuid         117
#define LINUX_SYS_getresuid         118
#define LINUX_SYS_setresgid         119
#define LINUX_SYS_getresgid         120
#define LINUX_SYS_getpgid           121
#define LINUX_SYS_setfsuid          122
#define LINUX_SYS_setfsgid          123
#define LINUX_SYS_getsid            124
#define LINUX_SYS_capget            125
#define LINUX_SYS_capset            126
#define LINUX_SYS_rt_sigpending     127
#define LINUX_SYS_rt_sigtimedwait   128
#define LINUX_SYS_rt_sigqueueinfo   129
#define LINUX_SYS_rt_sigsuspend     130
#define LINUX_SYS_sigaltstack       131
#define LINUX_SYS_utime             132
#define LINUX_SYS_mknod             133
#define LINUX_SYS_uselib            134
#define LINUX_SYS_personality       135
#define LINUX_SYS_ustat             136
#define LINUX_SYS_statfs            137
#define LINUX_SYS_fstatfs           138
#define LINUX_SYS_sysfs             139
#define LINUX_SYS_getpriority       140
#define LINUX_SYS_setpriority       141
#define LINUX_SYS_sched_setparam    142
#define LINUX_SYS_sched_getparam    143
#define LINUX_SYS_sched_setscheduler 144
#define LINUX_SYS_sched_getscheduler 145
#define LINUX_SYS_sched_get_priority_max 146
#define LINUX_SYS_sched_get_priority_min 147
#define LINUX_SYS_sched_rr_get_interval 148
#define LINUX_SYS_mlock             149
#define LINUX_SYS_munlock           150
#define LINUX_SYS_mlockall          151
#define LINUX_SYS_munlockall        152
#define LINUX_SYS_vhangup           153
#define LINUX_SYS_modify_ldt        154
#define LINUX_SYS_pivot_root        155
#define LINUX_SYS__sysctl           156
#define LINUX_SYS_prctl             157
#define LINUX_SYS_arch_prctl        158
#define LINUX_SYS_adjtimex          159
#define LINUX_SYS_setrlimit         160
#define LINUX_SYS_chroot            161
#define LINUX_SYS_sync              162
#define LINUX_SYS_acct              163
#define LINUX_SYS_settimeofday      164
#define LINUX_SYS_mount             165
#define LINUX_SYS_umount2           166
#define LINUX_SYS_swapon            167
#define LINUX_SYS_swapoff           168
#define LINUX_SYS_reboot            169
#define LINUX_SYS_sethostname       170
#define LINUX_SYS_setdomainname     171
#define LINUX_SYS_iopl              172
#define LINUX_SYS_ioperm            173
#define LINUX_SYS_create_module     174
#define LINUX_SYS_init_module       175
#define LINUX_SYS_delete_module     176
#define LINUX_SYS_get_kernel_syms   177
#define LINUX_SYS_query_module      178
#define LINUX_SYS_quotactl          179
#define LINUX_SYS_nfsservctl        180
#define LINUX_SYS_getpmsg           181
#define LINUX_SYS_putpmsg           182
#define LINUX_SYS_afs_syscall       183
#define LINUX_SYS_tuxcall           184
#define LINUX_SYS_security          185
#define LINUX_SYS_gettid            186
#define LINUX_SYS_readahead         187
#define LINUX_SYS_setxattr          188
#define LINUX_SYS_lsetxattr         189
#define LINUX_SYS_fsetxattr         190
#define LINUX_SYS_getxattr          191
#define LINUX_SYS_lgetxattr         192
#define LINUX_SYS_fgetxattr         193
#define LINUX_SYS_listxattr         194
#define LINUX_SYS_llistxattr        195
#define LINUX_SYS_flistxattr        196
#define LINUX_SYS_removexattr       197
#define LINUX_SYS_lremovexattr      198
#define LINUX_SYS_fremovexattr      199
#define LINUX_SYS_tkill             200
#define LINUX_SYS_time              201
#define LINUX_SYS_futex             202
#define LINUX_SYS_sched_setaffinity 203
#define LINUX_SYS_sched_getaffinity 204
#define LINUX_SYS_set_thread_area   205
#define LINUX_SYS_io_setup          206
#define LINUX_SYS_io_destroy        207
#define LINUX_SYS_io_getevents      208
#define LINUX_SYS_io_submit         209
#define LINUX_SYS_io_cancel         210
#define LINUX_SYS_get_thread_area   211
#define LINUX_SYS_lookup_dcookie    212
#define LINUX_SYS_epoll_create      213
#define LINUX_SYS_epoll_ctl_old     214
#define LINUX_SYS_epoll_wait_old    215
#define LINUX_SYS_remap_file_pages  216
#define LINUX_SYS_getdents64        217
#define LINUX_SYS_set_tid_address   218
#define LINUX_SYS_restart_syscall   219
#define LINUX_SYS_semtimedop        220
#define LINUX_SYS_fadvise64         221
#define LINUX_SYS_timer_create      222
#define LINUX_SYS_timer_settime     223
#define LINUX_SYS_timer_gettime     224
#define LINUX_SYS_timer_getoverrun  225
#define LINUX_SYS_timer_delete      226
#define LINUX_SYS_clock_settime     227
#define LINUX_SYS_clock_gettime     228
#define LINUX_SYS_clock_getres      229
#define LINUX_SYS_clock_nanosleep   230
#define LINUX_SYS_exit_group        231
#define LINUX_SYS_epoll_wait        232
#define LINUX_SYS_epoll_ctl         233
#define LINUX_SYS_tgkill            234
#define LINUX_SYS_utimes            235
#define LINUX_SYS_vserver           236
#define LINUX_SYS_mbind             237
#define LINUX_SYS_set_mempolicy     238
#define LINUX_SYS_get_mempolicy     239
#define LINUX_SYS_mq_open           240
#define LINUX_SYS_mq_unlink         241
#define LINUX_SYS_mq_timedsend      242
#define LINUX_SYS_mq_timedreceive   243
#define LINUX_SYS_mq_notify         244
#define LINUX_SYS_mq_getsetattr     245
#define LINUX_SYS_kexec_load        246
#define LINUX_SYS_waitid            247
#define LINUX_SYS_add_key           248
#define LINUX_SYS_request_key       249
#define LINUX_SYS_keyctl            250
#define LINUX_SYS_ioprio_set        251
#define LINUX_SYS_ioprio_get        252
#define LINUX_SYS_inotify_init      253
#define LINUX_SYS_inotify_add_watch 254
#define LINUX_SYS_inotify_rm_watch  255
#define LINUX_SYS_migrate_pages     256
#define LINUX_SYS_openat            257
#define LINUX_SYS_mkdirat           258
#define LINUX_SYS_mknodat           259
#define LINUX_SYS_fchownat          260
#define LINUX_SYS_futimesat         261
#define LINUX_SYS_newfstatat        262
#define LINUX_SYS_unlinkat          263
#define LINUX_SYS_renameat          264
#define LINUX_SYS_linkat            265
#define LINUX_SYS_symlinkat         266
#define LINUX_SYS_readlinkat        267
#define LINUX_SYS_fchmodat          268
#define LINUX_SYS_faccessat         269
#define LINUX_SYS_pselect6          270
#define LINUX_SYS_ppoll             271
#define LINUX_SYS_unshare           272
#define LINUX_SYS_set_robust_list   273
#define LINUX_SYS_get_robust_list   274
#define LINUX_SYS_splice            275
#define LINUX_SYS_tee               276
#define LINUX_SYS_sync_file_range   277
#define LINUX_SYS_vmsplice          278
#define LINUX_SYS_move_pages        279
#define LINUX_SYS_utimensat         280
#define LINUX_SYS_epoll_pwait       281
#define LINUX_SYS_signalfd          282
#define LINUX_SYS_timerfd_create    283
#define LINUX_SYS_eventfd           284
#define LINUX_SYS_fallocate         285
#define LINUX_SYS_timerfd_settime   286
#define LINUX_SYS_timerfd_gettime   287
#define LINUX_SYS_accept4           288
#define LINUX_SYS_signalfd4         289
#define LINUX_SYS_eventfd2          290
#define LINUX_SYS_epoll_create1     291
#define LINUX_SYS_dup3              292
#define LINUX_SYS_pipe2             293
#define LINUX_SYS_inotify_init1     294
#define LINUX_SYS_preadv            295
#define LINUX_SYS_pwritev           296
#define LINUX_SYS_rt_tgsigqueueinfo 297
#define LINUX_SYS_perf_event_open   298
#define LINUX_SYS_recvmmsg          299
#define LINUX_SYS_fanotify_init     300
#define LINUX_SYS_fanotify_mark     301
#define LINUX_SYS_prlimit64         302
#define LINUX_SYS_name_to_handle_at 303
#define LINUX_SYS_open_by_handle_at 304
#define LINUX_SYS_clock_adjtime     305
#define LINUX_SYS_syncfs            306
#define LINUX_SYS_sendmmsg          307
#define LINUX_SYS_setns             308
#define LINUX_SYS_getcpu            309
#define LINUX_SYS_process_vm_readv  310
#define LINUX_SYS_process_vm_writev 311
#define LINUX_SYS_kcmp              312
#define LINUX_SYS_finit_module      313
#define LINUX_SYS_sched_setattr     314
#define LINUX_SYS_sched_getattr     315
#define LINUX_SYS_renameat2         316
#define LINUX_SYS_seccomp           317
#define LINUX_SYS_getrandom         318
#define LINUX_SYS_memfd_create      319
#define LINUX_SYS_kexec_file_load   320
#define LINUX_SYS_bpf               321
#define LINUX_SYS_execveat          322
#define LINUX_SYS_userfaultfd       323
#define LINUX_SYS_membarrier        324
#define LINUX_SYS_mlock2            325
#define LINUX_SYS_copy_file_range   326
#define LINUX_SYS_preadv2           327
#define LINUX_SYS_pwritev2          328
#define LINUX_SYS_pkey_mprotect     329
#define LINUX_SYS_pkey_alloc        330
#define LINUX_SYS_pkey_free         331
#define LINUX_SYS_statx             332
#define LINUX_SYS_io_pgetevents     333
#define LINUX_SYS_rseq              334
#define LINUX_SYS_pidfd_send_signal 424
#define LINUX_SYS_io_uring_setup    425
#define LINUX_SYS_io_uring_enter    426
#define LINUX_SYS_io_uring_register 427
#define LINUX_SYS_open_tree         428
#define LINUX_SYS_move_mount        429
#define LINUX_SYS_fsopen            430
#define LINUX_SYS_fsconfig          431
#define LINUX_SYS_fsmount           432
#define LINUX_SYS_fspick            433
#define LINUX_SYS_pidfd_open        434
#define LINUX_SYS_clone3            435

#define LINUX_SYS_MAX               436

// =============================================================================
// LINUX-SPECIFIC STRUCTURES
// =============================================================================

// Linux stat structure (64-bit)
struct linux_stat {
    uint64_t st_dev;
    uint64_t st_ino;
    uint64_t st_nlink;
    uint32_t st_mode;
    uint32_t st_uid;
    uint32_t st_gid;
    uint32_t __pad0;
    uint64_t st_rdev;
    int64_t  st_size;
    int64_t  st_blksize;
    int64_t  st_blocks;
    struct {
        int64_t tv_sec;
        int64_t tv_nsec;
    } st_atim;
    struct {
        int64_t tv_sec;
        int64_t tv_nsec;
    } st_mtim;
    struct {
        int64_t tv_sec;
        int64_t tv_nsec;
    } st_ctim;
    int64_t  __unused[3];
};

// Linux clone flags
#define LINUX_CLONE_VM              0x00000100
#define LINUX_CLONE_FS              0x00000200
#define LINUX_CLONE_FILES           0x00000400
#define LINUX_CLONE_SIGHAND         0x00000800
#define LINUX_CLONE_PTRACE          0x00002000
#define LINUX_CLONE_VFORK           0x00004000
#define LINUX_CLONE_PARENT          0x00008000
#define LINUX_CLONE_THREAD          0x00010000
#define LINUX_CLONE_NEWNS           0x00020000
#define LINUX_CLONE_SYSVSEM         0x00040000
#define LINUX_CLONE_SETTLS          0x00080000
#define LINUX_CLONE_PARENT_SETTID   0x00100000
#define LINUX_CLONE_CHILD_CLEARTID  0x00200000
#define LINUX_CLONE_DETACHED        0x00400000
#define LINUX_CLONE_UNTRACED        0x00800000
#define LINUX_CLONE_CHILD_SETTID    0x01000000
#define LINUX_CLONE_NEWCGROUP       0x02000000
#define LINUX_CLONE_NEWUTS          0x04000000
#define LINUX_CLONE_NEWIPC          0x08000000
#define LINUX_CLONE_NEWUSER         0x10000000
#define LINUX_CLONE_NEWPID          0x20000000
#define LINUX_CLONE_NEWNET          0x40000000
#define LINUX_CLONE_IO              0x80000000

// Linux futex operations
#define LINUX_FUTEX_WAIT            0
#define LINUX_FUTEX_WAKE            1
#define LINUX_FUTEX_FD              2
#define LINUX_FUTEX_REQUEUE         3
#define LINUX_FUTEX_CMP_REQUEUE     4
#define LINUX_FUTEX_WAKE_OP         5
#define LINUX_FUTEX_LOCK_PI         6
#define LINUX_FUTEX_UNLOCK_PI       7
#define LINUX_FUTEX_TRYLOCK_PI      8
#define LINUX_FUTEX_WAIT_BITSET     9
#define LINUX_FUTEX_WAKE_BITSET     10

// Linux file flags
#define LINUX_O_RDONLY      0x00000
#define LINUX_O_WRONLY      0x00001
#define LINUX_O_RDWR        0x00002
#define LINUX_O_CREAT       0x00040
#define LINUX_O_EXCL        0x00080
#define LINUX_O_NOCTTY      0x00100
#define LINUX_O_TRUNC       0x00200
#define LINUX_O_APPEND      0x00400
#define LINUX_O_NONBLOCK    0x00800
#define LINUX_O_DSYNC       0x01000
#define LINUX_O_DIRECT      0x04000
#define LINUX_O_LARGEFILE   0x08000
#define LINUX_O_DIRECTORY   0x10000
#define LINUX_O_NOFOLLOW    0x20000
#define LINUX_O_NOATIME     0x40000
#define LINUX_O_CLOEXEC     0x80000

// Linux mmap flags
#define LINUX_MAP_SHARED        0x01
#define LINUX_MAP_PRIVATE       0x02
#define LINUX_MAP_SHARED_VALIDATE 0x03
#define LINUX_MAP_TYPE          0x0f
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

// =============================================================================
// FUNCTION PROTOTYPES
// =============================================================================

// Initialize Linux personality
void linux_personality_init(void);

// Core syscall handlers
long sys_linux_read(unsigned int fd, char *buf, size_t count);
long sys_linux_write(unsigned int fd, const char *buf, size_t count);
long sys_linux_open(const char *pathname, int flags, mode_t mode);
long sys_linux_close(unsigned int fd);
long sys_linux_stat(const char *pathname, struct linux_stat *statbuf);
long sys_linux_fstat(unsigned int fd, struct linux_stat *statbuf);
long sys_linux_lstat(const char *pathname, struct linux_stat *statbuf);
long sys_linux_mmap(unsigned long addr, unsigned long len, unsigned long prot,
                    unsigned long flags, unsigned long fd, unsigned long off);
long sys_linux_getpid(void);
long sys_linux_fork(void);
long sys_linux_vfork(void);
long sys_linux_clone(unsigned long flags, void *child_stack, int *ptid, int *ctid, unsigned long newtls);
long sys_linux_execve(const char *pathname, char *const argv[], char *const envp[]);
long sys_linux_exit(int status);
long sys_linux_exit_group(int status);

// Extended syscalls
long sys_linux_futex(int *uaddr, int op, int val, struct timespec *timeout, int *uaddr2, int val3);
long sys_linux_epoll_create(int size);
long sys_linux_epoll_create1(int flags);
long sys_linux_epoll_ctl(int epfd, int op, int fd, struct epoll_event *event);
long sys_linux_epoll_wait(int epfd, struct epoll_event *events, int maxevents, int timeout);
long sys_linux_eventfd(unsigned int initval);
long sys_linux_eventfd2(unsigned int initval, int flags);
long sys_linux_signalfd(int fd, const sigset_t *mask, int flags);
long sys_linux_timerfd_create(int clockid, int flags);
long sys_linux_inotify_init(void);
long sys_linux_inotify_init1(int flags);
long sys_linux_inotify_add_watch(int fd, const char *pathname, uint32_t mask);
long sys_linux_inotify_rm_watch(int fd, int wd);

// io_uring syscalls
long sys_linux_io_uring_setup(unsigned entries, struct io_uring_params *params);
long sys_linux_io_uring_enter(int fd, unsigned to_submit, unsigned min_complete, unsigned flags, sigset_t *sig);
long sys_linux_io_uring_register(int fd, unsigned opcode, void *arg, unsigned nr_args);

// Translation functions
int translate_linux_open_flags(int flags);
int translate_linux_mmap_flags(int flags);
int translate_linux_mmap_prot(int prot);
int translate_linux_clone_flags(unsigned long flags);
int translate_linux_stat(void *src, void *dst, int direction);
int translate_linux_errno(int native_errno);

// Compatibility helpers
int linux_to_native_signal(int linux_sig);
int native_to_linux_signal(int native_sig);

// =============================================================================
// SYSCALL TABLE DECLARATION
// =============================================================================

extern const syscall_entry_t linux_syscall_table[];
extern const unsigned int linux_syscall_table_size;

#endif // SYSCALL_LINUX_H
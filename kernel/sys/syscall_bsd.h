/**
 * @file syscall_bsd.h  
 * @brief BSD syscall compatibility layer
 * 
 * Provides FreeBSD/NetBSD/OpenBSD syscall definitions and structures
 * for BSD binary compatibility.
 */

#pragma once

#include <stdint.h>
#include <stddef.h>
#include "syscall_gateway.h"

// =============================================================================
// BSD SYSCALL NUMBERS (FreeBSD 14.x base)
// =============================================================================

#define BSD_SYS_syscall             0
#define BSD_SYS_exit                1
#define BSD_SYS_fork                2
#define BSD_SYS_read                3
#define BSD_SYS_write               4
#define BSD_SYS_open                5
#define BSD_SYS_close               6
#define BSD_SYS_wait4               7
#define BSD_SYS_link                9
#define BSD_SYS_unlink              10
#define BSD_SYS_chdir               12
#define BSD_SYS_fchdir              13
#define BSD_SYS_freebsd11_mknod     14
#define BSD_SYS_chmod               15
#define BSD_SYS_chown               16
#define BSD_SYS_break               17
#define BSD_SYS_getpid              20
#define BSD_SYS_mount               21
#define BSD_SYS_unmount             22
#define BSD_SYS_setuid              23
#define BSD_SYS_getuid              24
#define BSD_SYS_geteuid             25
#define BSD_SYS_ptrace              26
#define BSD_SYS_recvmsg             27
#define BSD_SYS_sendmsg             28
#define BSD_SYS_recvfrom            29
#define BSD_SYS_accept              30
#define BSD_SYS_getpeername         31
#define BSD_SYS_getsockname         32
#define BSD_SYS_access              33
#define BSD_SYS_chflags             34
#define BSD_SYS_fchflags            35
#define BSD_SYS_sync                36
#define BSD_SYS_kill                37
#define BSD_SYS_getppid             39
#define BSD_SYS_dup                 41
#define BSD_SYS_freebsd10_pipe      42
#define BSD_SYS_getegid             43
#define BSD_SYS_profil              44
#define BSD_SYS_ktrace              45
#define BSD_SYS_getgid              47
#define BSD_SYS_getlogin            49
#define BSD_SYS_setlogin            50
#define BSD_SYS_acct                51
#define BSD_SYS_sigaltstack         53
#define BSD_SYS_ioctl               54
#define BSD_SYS_reboot              55
#define BSD_SYS_revoke              56
#define BSD_SYS_symlink             57
#define BSD_SYS_readlink            58
#define BSD_SYS_execve              59
#define BSD_SYS_umask               60
#define BSD_SYS_chroot              61
#define BSD_SYS_msync               65
#define BSD_SYS_vfork               66
#define BSD_SYS_munmap              73
#define BSD_SYS_mprotect            74
#define BSD_SYS_madvise             75
#define BSD_SYS_mincore             78
#define BSD_SYS_getgroups           79
#define BSD_SYS_setgroups           80
#define BSD_SYS_getpgrp             81
#define BSD_SYS_setpgid             82
#define BSD_SYS_setitimer           83
#define BSD_SYS_swapon              85
#define BSD_SYS_getitimer           86
#define BSD_SYS_getdtablesize       89
#define BSD_SYS_dup2                90
#define BSD_SYS_fcntl               92
#define BSD_SYS_select              93
#define BSD_SYS_fsync               95
#define BSD_SYS_setpriority         96
#define BSD_SYS_socket              97
#define BSD_SYS_connect             98
#define BSD_SYS_getpriority         100
#define BSD_SYS_bind                104
#define BSD_SYS_setsockopt          105
#define BSD_SYS_listen              106
#define BSD_SYS_gettimeofday        116
#define BSD_SYS_getrusage           117
#define BSD_SYS_getsockopt          118
#define BSD_SYS_readv               120
#define BSD_SYS_writev              121
#define BSD_SYS_settimeofday        122
#define BSD_SYS_fchown              123
#define BSD_SYS_fchmod              124
#define BSD_SYS_setreuid            126
#define BSD_SYS_setregid            127
#define BSD_SYS_rename              128
#define BSD_SYS_flock               131
#define BSD_SYS_mkfifo              132
#define BSD_SYS_sendto              133
#define BSD_SYS_shutdown            134
#define BSD_SYS_socketpair          135
#define BSD_SYS_mkdir               136
#define BSD_SYS_rmdir               137
#define BSD_SYS_utimes              138
#define BSD_SYS_adjtime             140
#define BSD_SYS_setsid              147
#define BSD_SYS_quotactl            148
#define BSD_SYS_nlm_syscall         154
#define BSD_SYS_nfssvc              155
#define BSD_SYS_lgetfh              160
#define BSD_SYS_getfh               161
#define BSD_SYS_sysarch             165
#define BSD_SYS_rtprio              166
#define BSD_SYS_semsys              169
#define BSD_SYS_msgsys              170
#define BSD_SYS_shmsys              171
#define BSD_SYS_setfib              175
#define BSD_SYS_ntp_adjtime         176
#define BSD_SYS_setgid              181
#define BSD_SYS_setegid             182
#define BSD_SYS_seteuid             183
#define BSD_SYS_freebsd11_stat      188
#define BSD_SYS_freebsd11_fstat     189
#define BSD_SYS_freebsd11_lstat     190
#define BSD_SYS_pathconf            191
#define BSD_SYS_fpathconf           192
#define BSD_SYS_getrlimit           194
#define BSD_SYS_setrlimit           195
#define BSD_SYS_freebsd11_getdirentries 196
#define BSD_SYS_freebsd6_mmap       197
#define BSD_SYS_freebsd6_lseek      199
#define BSD_SYS_freebsd6_truncate   200
#define BSD_SYS_freebsd6_ftruncate  201
#define BSD_SYS___sysctl            202
#define BSD_SYS_mlock               203
#define BSD_SYS_munlock             204
#define BSD_SYS_undelete            205
#define BSD_SYS_futimes             206
#define BSD_SYS_getpgid             207
#define BSD_SYS_poll                209
#define BSD_SYS_freebsd7___semctl   220
#define BSD_SYS_semget              221
#define BSD_SYS_semop               222
#define BSD_SYS_freebsd7_msgctl     224
#define BSD_SYS_msgget              225
#define BSD_SYS_msgsnd              226
#define BSD_SYS_msgrcv              227
#define BSD_SYS_shmat               228
#define BSD_SYS_freebsd7_shmctl     229
#define BSD_SYS_shmdt               230
#define BSD_SYS_shmget              231
#define BSD_SYS_clock_gettime       232
#define BSD_SYS_clock_settime       233
#define BSD_SYS_clock_getres        234
#define BSD_SYS_ktimer_create       235
#define BSD_SYS_ktimer_delete       236
#define BSD_SYS_ktimer_settime      237
#define BSD_SYS_ktimer_gettime      238
#define BSD_SYS_ktimer_getoverrun   239
#define BSD_SYS_nanosleep           240
#define BSD_SYS_ffclock_getcounter  241
#define BSD_SYS_ffclock_setestimate 242
#define BSD_SYS_ffclock_getestimate 243
#define BSD_SYS_clock_nanosleep     244
#define BSD_SYS_clock_getcpuclockid2 247
#define BSD_SYS_ntp_gettime         248
#define BSD_SYS_minherit            250
#define BSD_SYS_rfork               251
#define BSD_SYS_issetugid           253
#define BSD_SYS_lchown              254
#define BSD_SYS_aio_read            255
#define BSD_SYS_aio_write           256
#define BSD_SYS_lio_listio          257
#define BSD_SYS_freebsd11_getdents  272
#define BSD_SYS_lchmod              274
#define BSD_SYS_lutimes             276
#define BSD_SYS_freebsd11_nstat     278
#define BSD_SYS_freebsd11_nfstat    279
#define BSD_SYS_freebsd11_nlstat    280
#define BSD_SYS_preadv              289
#define BSD_SYS_pwritev             290
#define BSD_SYS_fhopen              298
#define BSD_SYS_modnext             300
#define BSD_SYS_modstat             301
#define BSD_SYS_modfnext            302
#define BSD_SYS_modfind             303
#define BSD_SYS_kldload             304
#define BSD_SYS_kldunload           305
#define BSD_SYS_kldfind             306
#define BSD_SYS_kldnext             307
#define BSD_SYS_kldstat             308
#define BSD_SYS_kldfirstmod         309
#define BSD_SYS_getsid              310
#define BSD_SYS_setresuid           311
#define BSD_SYS_setresgid           312
#define BSD_SYS_aio_return          314
#define BSD_SYS_aio_suspend         315
#define BSD_SYS_aio_cancel          316
#define BSD_SYS_aio_error           317
#define BSD_SYS_yield               321
#define BSD_SYS_mlockall            324
#define BSD_SYS_munlockall          325
#define BSD_SYS___getcwd            326
#define BSD_SYS_sched_setparam      327
#define BSD_SYS_sched_getparam      328
#define BSD_SYS_sched_setscheduler  329
#define BSD_SYS_sched_getscheduler  330
#define BSD_SYS_sched_yield         331
#define BSD_SYS_sched_get_priority_max 332
#define BSD_SYS_sched_get_priority_min 333
#define BSD_SYS_sched_rr_get_interval 334
#define BSD_SYS_utrace              335
#define BSD_SYS_kldsym              337
#define BSD_SYS_jail                338
#define BSD_SYS_nnpfs_syscall       339
#define BSD_SYS_sigprocmask         340
#define BSD_SYS_sigsuspend          341
#define BSD_SYS_sigpending          343
#define BSD_SYS_sigtimedwait        345
#define BSD_SYS_sigwaitinfo         346
#define BSD_SYS___acl_get_file      347
#define BSD_SYS___acl_set_file      348
#define BSD_SYS___acl_get_fd        349
#define BSD_SYS___acl_set_fd        350
#define BSD_SYS___acl_delete_file   351
#define BSD_SYS___acl_delete_fd     352
#define BSD_SYS___acl_aclcheck_file 353
#define BSD_SYS___acl_aclcheck_fd   354
#define BSD_SYS_extattrctl          355
#define BSD_SYS_extattr_set_file    356
#define BSD_SYS_extattr_get_file    357
#define BSD_SYS_extattr_delete_file 358
#define BSD_SYS_aio_waitcomplete    359
#define BSD_SYS_getresuid           360
#define BSD_SYS_getresgid           361
#define BSD_SYS_kqueue              362
#define BSD_SYS_freebsd11_kevent    363
#define BSD_SYS_extattr_set_fd      371
#define BSD_SYS_extattr_get_fd      372
#define BSD_SYS_extattr_delete_fd   373
#define BSD_SYS___setugid           374
#define BSD_SYS_eaccess             376
#define BSD_SYS_afs3_syscall        377
#define BSD_SYS_nmount              378
#define BSD_SYS___mac_get_proc      384
#define BSD_SYS___mac_set_proc      385
#define BSD_SYS___mac_get_fd        386
#define BSD_SYS___mac_get_file      387
#define BSD_SYS___mac_set_fd        388
#define BSD_SYS___mac_set_file      389
#define BSD_SYS_kenv                390
#define BSD_SYS_lchflags            391
#define BSD_SYS_uuidgen             392
#define BSD_SYS_sendfile            393
#define BSD_SYS_mac_syscall         394
#define BSD_SYS_ksem_close          400
#define BSD_SYS_ksem_post           401
#define BSD_SYS_ksem_wait           402
#define BSD_SYS_ksem_trywait        403
#define BSD_SYS_ksem_init           404
#define BSD_SYS_ksem_open           405
#define BSD_SYS_ksem_unlink         406
#define BSD_SYS_ksem_getvalue       407
#define BSD_SYS_ksem_destroy        408
#define BSD_SYS___mac_get_pid       409
#define BSD_SYS___mac_get_link      410
#define BSD_SYS___mac_set_link      411
#define BSD_SYS_extattr_set_link    412
#define BSD_SYS_extattr_get_link    413
#define BSD_SYS_extattr_delete_link 414
#define BSD_SYS___mac_execve        415
#define BSD_SYS_sigaction           416
#define BSD_SYS_sigreturn           417
#define BSD_SYS_getcontext          421
#define BSD_SYS_setcontext          422
#define BSD_SYS_swapcontext         423
#define BSD_SYS_swapoff             424
#define BSD_SYS___acl_get_link      425
#define BSD_SYS___acl_set_link      426
#define BSD_SYS___acl_delete_link   427
#define BSD_SYS___acl_aclcheck_link 428
#define BSD_SYS_sigwait             429
#define BSD_SYS_thr_create          430
#define BSD_SYS_thr_exit            431
#define BSD_SYS_thr_self            432
#define BSD_SYS_thr_kill            433
#define BSD_SYS_jail_attach         436
#define BSD_SYS_extattr_list_fd     437
#define BSD_SYS_extattr_list_file   438
#define BSD_SYS_extattr_list_link   439
#define BSD_SYS_ksem_timedwait      441
#define BSD_SYS_thr_suspend         442
#define BSD_SYS_thr_wake            443
#define BSD_SYS_kldunloadf          444
#define BSD_SYS_audit               445
#define BSD_SYS_auditon             446
#define BSD_SYS_getauid             447
#define BSD_SYS_setauid             448
#define BSD_SYS_getaudit            449
#define BSD_SYS_setaudit            450
#define BSD_SYS_getaudit_addr       451
#define BSD_SYS_setaudit_addr       452
#define BSD_SYS_auditctl            453
#define BSD_SYS__umtx_op            454
#define BSD_SYS_thr_new             455
#define BSD_SYS_sigqueue            456
#define BSD_SYS_kmq_open            457
#define BSD_SYS_kmq_setattr         458
#define BSD_SYS_kmq_timedreceive    459
#define BSD_SYS_kmq_timedsend       460
#define BSD_SYS_kmq_notify          461
#define BSD_SYS_kmq_unlink          462
#define BSD_SYS_abort2              463
#define BSD_SYS_thr_set_name        464
#define BSD_SYS_aio_fsync           465
#define BSD_SYS_rtprio_thread       466
#define BSD_SYS_sctp_peeloff        471
#define BSD_SYS_sctp_generic_sendmsg 472
#define BSD_SYS_sctp_generic_sendmsg_iov 473
#define BSD_SYS_sctp_generic_recvmsg 474
#define BSD_SYS_pread               475
#define BSD_SYS_pwrite              476
#define BSD_SYS_mmap                477
#define BSD_SYS_lseek               478
#define BSD_SYS_truncate            479
#define BSD_SYS_ftruncate           480
#define BSD_SYS_thr_kill2           481
#define BSD_SYS_freebsd12_shm_open  482
#define BSD_SYS_shm_unlink          483
#define BSD_SYS_cpuset              484
#define BSD_SYS_cpuset_setid        485
#define BSD_SYS_cpuset_getid        486
#define BSD_SYS_cpuset_getaffinity  487
#define BSD_SYS_cpuset_setaffinity  488
#define BSD_SYS_faccessat           489
#define BSD_SYS_fchmodat            490
#define BSD_SYS_fchownat            491
#define BSD_SYS_fexecve             492
#define BSD_SYS_freebsd11_fstatat   493
#define BSD_SYS_futimesat           494
#define BSD_SYS_linkat              495
#define BSD_SYS_mkdirat             496
#define BSD_SYS_mkfifoat            497
#define BSD_SYS_freebsd11_mknodat   498
#define BSD_SYS_openat              499
#define BSD_SYS_readlinkat          500
#define BSD_SYS_renameat            501
#define BSD_SYS_symlinkat           502
#define BSD_SYS_unlinkat            503
#define BSD_SYS_posix_openpt        504
#define BSD_SYS_gssd_syscall        505
#define BSD_SYS_jail_get            506
#define BSD_SYS_jail_set            507
#define BSD_SYS_jail_remove         508
#define BSD_SYS_closefrom           509
#define BSD_SYS___semctl            510
#define BSD_SYS_msgctl              511
#define BSD_SYS_shmctl              512
#define BSD_SYS_lpathconf           513
#define BSD_SYS___cap_rights_get    515
#define BSD_SYS_cap_enter           516
#define BSD_SYS_cap_getmode         517
#define BSD_SYS_pdfork              518
#define BSD_SYS_pdkill              519
#define BSD_SYS_pdgetpid            520
#define BSD_SYS_pselect             522
#define BSD_SYS_getloginclass       523
#define BSD_SYS_setloginclass       524
#define BSD_SYS_rctl_get_racct      525
#define BSD_SYS_rctl_get_rules      526
#define BSD_SYS_rctl_get_limits     527
#define BSD_SYS_rctl_add_rule       528
#define BSD_SYS_rctl_remove_rule    529
#define BSD_SYS_posix_fallocate     530
#define BSD_SYS_posix_fadvise       531
#define BSD_SYS_wait6               532
#define BSD_SYS_cap_rights_limit    533
#define BSD_SYS_cap_ioctls_limit    534
#define BSD_SYS_cap_ioctls_get      535
#define BSD_SYS_cap_fcntls_limit    536
#define BSD_SYS_cap_fcntls_get      537
#define BSD_SYS_bindat              538
#define BSD_SYS_connectat           539
#define BSD_SYS_chflagsat           540
#define BSD_SYS_accept4             541
#define BSD_SYS_pipe2               542
#define BSD_SYS_aio_mlock           543
#define BSD_SYS_procctl             544
#define BSD_SYS_ppoll               545
#define BSD_SYS_futimens            546
#define BSD_SYS_utimensat           547
#define BSD_SYS_fdatasync           550
#define BSD_SYS_fstat               551
#define BSD_SYS_fstatat             552
#define BSD_SYS_fhstat              553
#define BSD_SYS_getdirentries       554
#define BSD_SYS_statfs              555
#define BSD_SYS_fstatfs             556
#define BSD_SYS_getfsstat           557
#define BSD_SYS_fhstatfs            558
#define BSD_SYS_mknodat             559
#define BSD_SYS_kevent              560
#define BSD_SYS_cpuset_getdomain    561
#define BSD_SYS_cpuset_setdomain    562
#define BSD_SYS_getrandom           563
#define BSD_SYS_getfhat             564
#define BSD_SYS_fhlink              565
#define BSD_SYS_fhlinkat            566
#define BSD_SYS_fhreadlink          567
#define BSD_SYS_funlinkat           568
#define BSD_SYS_copy_file_range     569
#define BSD_SYS___sysctlbyname      570
#define BSD_SYS_shm_open2           571
#define BSD_SYS_shm_rename          572
#define BSD_SYS_sigfastblock        573
#define BSD_SYS___realpathat        574
#define BSD_SYS_close_range         575
#define BSD_SYS_rpctls_syscall      576
#define BSD_SYS___specialfd         577
#define BSD_SYS_aio_writev          578
#define BSD_SYS_aio_readv           579
#define BSD_SYS_fspacectl           580
#define BSD_SYS_sched_getcpu        581

#define BSD_SYS_MAX                 582

// =============================================================================
// BSD-SPECIFIC STRUCTURES
// =============================================================================

// BSD stat structure
struct bsd_stat {
    uint32_t st_dev;
    uint32_t st_ino;
    uint16_t st_mode;
    uint16_t st_nlink;
    uint32_t st_uid;
    uint32_t st_gid;
    uint32_t st_rdev;
    struct {
        int32_t tv_sec;
        int32_t tv_nsec;
    } st_atim;
    struct {
        int32_t tv_sec;
        int32_t tv_nsec;
    } st_mtim;
    struct {
        int32_t tv_sec;
        int32_t tv_nsec;
    } st_ctim;
    int64_t st_size;
    int64_t st_blocks;
    int32_t st_blksize;
    uint32_t st_flags;  // BSD-specific: file flags
    uint32_t st_gen;     // BSD-specific: generation number
    int32_t st_lspare;
    struct {
        int64_t tv_sec;
        int64_t tv_nsec;
    } st_birthtim;       // BSD-specific: birth time
};

// BSD kqueue event structure
struct bsd_kevent {
    uintptr_t ident;     // Identifier for event
    int16_t filter;      // Filter for event
    uint16_t flags;      // General flags
    uint32_t fflags;     // Filter-specific flags
    intptr_t data;       // Filter-specific data
    void *udata;         // User-defined data
};

// BSD jail structure
struct bsd_jail {
    uint32_t version;
    char *path;
    char *hostname;
    char *jailname;
    uint32_t ip4s;
    uint32_t ip6s;
    struct in_addr *ip4;
    struct in6_addr *ip6;
};

// BSD rfork flags
#define BSD_RFNAMEG     0x00001  // New nameidata group
#define BSD_RFENVG      0x00002  // New environment group  
#define BSD_RFFDG       0x00004  // Copy fd table
#define BSD_RFNOTEG     0x00008  // New note group
#define BSD_RFPROC      0x00010  // New process
#define BSD_RFMEM       0x00020  // Share address space
#define BSD_RFNOWAIT    0x00040  // Parent need not wait
#define BSD_RFCNAMEG    0x00100  // Clean nameidata group
#define BSD_RFCENVG     0x00200  // Clean environment group
#define BSD_RFCFDG      0x00400  // Close all fds
#define BSD_RFTHREAD    0x00800  // Create thread
#define BSD_RFSIGSHARE  0x01000  // Share signal handlers

// BSD kqueue filters
#define BSD_EVFILT_READ     (-1)
#define BSD_EVFILT_WRITE    (-2)
#define BSD_EVFILT_AIO      (-3)
#define BSD_EVFILT_VNODE    (-4)
#define BSD_EVFILT_PROC     (-5)
#define BSD_EVFILT_SIGNAL   (-6)
#define BSD_EVFILT_TIMER    (-7)
#define BSD_EVFILT_PROCDESC (-8)
#define BSD_EVFILT_FS       (-9)
#define BSD_EVFILT_LIO      (-10)
#define BSD_EVFILT_USER     (-11)
#define BSD_EVFILT_SENDFILE (-12)

// BSD kqueue flags
#define BSD_EV_ADD      0x0001
#define BSD_EV_DELETE   0x0002
#define BSD_EV_ENABLE   0x0004
#define BSD_EV_DISABLE  0x0008
#define BSD_EV_ONESHOT  0x0010
#define BSD_EV_CLEAR    0x0020
#define BSD_EV_RECEIPT  0x0040
#define BSD_EV_DISPATCH 0x0080
#define BSD_EV_SYSFLAGS 0xF000
#define BSD_EV_FLAG1    0x2000
#define BSD_EV_EOF      0x8000
#define BSD_EV_ERROR    0x4000

// =============================================================================
// FUNCTION PROTOTYPES
// =============================================================================

// Initialize BSD personality
void bsd_personality_init(void);

// Core syscall handlers
long sys_bsd_read(int fd, void *buf, size_t count);
long sys_bsd_write(int fd, const void *buf, size_t count);
long sys_bsd_open(const char *path, int flags, mode_t mode);
long sys_bsd_close(int fd);
long sys_bsd_stat(const char *path, struct bsd_stat *sb);
long sys_bsd_fstat(int fd, struct bsd_stat *sb);
long sys_bsd_lstat(const char *path, struct bsd_stat *sb);
long sys_bsd_mmap(void *addr, size_t len, int prot, int flags, int fd, off_t offset);
long sys_bsd_getpid(void);
long sys_bsd_fork(void);
long sys_bsd_vfork(void);
long sys_bsd_rfork(int flags);
long sys_bsd_execve(const char *path, char *const argv[], char *const envp[]);
long sys_bsd_exit(int status);

// BSD-specific syscalls
long sys_bsd_kqueue(void);
long sys_bsd_kevent(int kq, const struct bsd_kevent *changelist, int nchanges,
                    struct bsd_kevent *eventlist, int nevents, const struct timespec *timeout);
long sys_bsd_jail(struct bsd_jail *jail);
long sys_bsd_jail_attach(int jid);
long sys_bsd_jail_get(struct iovec *iovp, unsigned int iovcnt, int flags);
long sys_bsd_jail_set(struct iovec *iovp, unsigned int iovcnt, int flags);
long sys_bsd_jail_remove(int jid);
long sys_bsd_cap_enter(void);
long sys_bsd_cap_getmode(unsigned int *modep);
long sys_bsd_cap_rights_limit(int fd, const cap_rights_t *rights);
long sys_bsd_cpuset(int *setid);
long sys_bsd_cpuset_setid(int which, int id, int setid);
long sys_bsd_cpuset_getid(int level, int which, int id, int *setid);
long sys_bsd_cpuset_getaffinity(int level, int which, int id, size_t cpusetsize, cpuset_t *mask);
long sys_bsd_cpuset_setaffinity(int level, int which, int id, size_t cpusetsize, const cpuset_t *mask);

// Translation functions
int translate_bsd_open_flags(int flags);
int translate_bsd_mmap_flags(int flags);
int translate_bsd_rfork_flags(int flags);
int translate_bsd_stat(void *src, void *dst, int direction);
int translate_bsd_errno(int native_errno);

// Compatibility helpers
int bsd_to_native_signal(int bsd_sig);
int native_to_bsd_signal(int native_sig);

// =============================================================================
// SYSCALL TABLE DECLARATION
// =============================================================================

extern const syscall_entry_t bsd_syscall_table[];
extern const unsigned int bsd_syscall_table_size;

#endif // SYSCALL_BSD_H
#ifndef LINUX_COMPAT_H
#define LINUX_COMPAT_H

/* Linux x86_64 System Call Numbers */

#define LINUX_SYS_read          0
#define LINUX_SYS_write         1
#define LINUX_SYS_open          2
#define LINUX_SYS_close         3
#define LINUX_SYS_stat          4
#define LINUX_SYS_fstat         5
#define LINUX_SYS_lstat         6
#define LINUX_SYS_poll          7
#define LINUX_SYS_lseek         8
#define LINUX_SYS_mmap          9
#define LINUX_SYS_mprotect      10
#define LINUX_SYS_munmap        11
#define LINUX_SYS_brk           12
#define LINUX_SYS_rt_sigaction  13
#define LINUX_SYS_rt_sigprocmask 14
#define LINUX_SYS_rt_sigreturn  15
#define LINUX_SYS_ioctl         16
#define LINUX_SYS_pread64       17
#define LINUX_SYS_pwrite64      18
#define LINUX_SYS_readv         19
#define LINUX_SYS_writev        20
#define LINUX_SYS_access        21
#define LINUX_SYS_pipe          22
#define LINUX_SYS_select        23
#define LINUX_SYS_sched_yield   24
#define LINUX_SYS_mremap        25
#define LINUX_SYS_msync         26
#define LINUX_SYS_mincore       27
#define LINUX_SYS_madvise       28
#define LINUX_SYS_shmget        29
#define LINUX_SYS_shmat         30
#define LINUX_SYS_shmctl        31
#define LINUX_SYS_dup           32
#define LINUX_SYS_dup2          33
#define LINUX_SYS_pause         34
#define LINUX_SYS_nanosleep     35
#define LINUX_SYS_getitimer     36
#define LINUX_SYS_alarm         37
#define LINUX_SYS_setitimer     38
#define LINUX_SYS_getpid        39
#define LINUX_SYS_sendfile      40
#define LINUX_SYS_socket        41
#define LINUX_SYS_connect       42
#define LINUX_SYS_accept        43
#define LINUX_SYS_sendto        44
#define LINUX_SYS_recvfrom      45
#define LINUX_SYS_sendmsg       46
#define LINUX_SYS_recvmsg       47
#define LINUX_SYS_shutdown      48
#define LINUX_SYS_bind          49
#define LINUX_SYS_listen        50
#define LINUX_SYS_getsockname   51
#define LINUX_SYS_getpeername   52
#define LINUX_SYS_socketpair    53
#define LINUX_SYS_setsockopt    54
#define LINUX_SYS_getsockopt    55
#define LINUX_SYS_clone         56
#define LINUX_SYS_fork          57
#define LINUX_SYS_vfork         58
#define LINUX_SYS_execve        59
#define LINUX_SYS_exit          60
#define LINUX_SYS_wait4         61
#define LINUX_SYS_kill          62
#define LINUX_SYS_uname         63
#define LINUX_SYS_semget        64
#define LINUX_SYS_semop         65
#define LINUX_SYS_semctl        66
#define LINUX_SYS_shmdt         67
#define LINUX_SYS_msgget        68
#define LINUX_SYS_msgsnd        69
#define LINUX_SYS_msgrcv        70
#define LINUX_SYS_msgctl        71
#define LINUX_SYS_fcntl         72
#define LINUX_SYS_flock         73
#define LINUX_SYS_fsync         74
#define LINUX_SYS_fdatasync     75
#define LINUX_SYS_truncate      76
#define LINUX_SYS_ftruncate     77
#define LINUX_SYS_getdents      78
#define LINUX_SYS_getcwd        79
#define LINUX_SYS_chdir         80
#define LINUX_SYS_fchdir        81
#define LINUX_SYS_rename        82
#define LINUX_SYS_mkdir         83
#define LINUX_SYS_rmdir         84
#define LINUX_SYS_creat         85
#define LINUX_SYS_link          86
#define LINUX_SYS_unlink        87
#define LINUX_SYS_symlink       88
#define LINUX_SYS_readlink      89
#define LINUX_SYS_chmod         90
#define LINUX_SYS_fchmod        91
#define LINUX_SYS_chown         92
#define LINUX_SYS_fchown        93
#define LINUX_SYS_lchown        94
#define LINUX_SYS_umask         95
#define LINUX_SYS_gettimeofday  96
#define LINUX_SYS_getrlimit     97
#define LINUX_SYS_getrusage     98
#define LINUX_SYS_sysinfo       99
#define LINUX_SYS_times         100

/* Struct definitions for compat */
struct linux_stat {
    unsigned long st_dev;
    unsigned long st_ino;
    unsigned long st_nlink;
    unsigned int  st_mode;
    unsigned int  st_uid;
    unsigned int  st_gid;
    unsigned int  __pad0;
    unsigned long st_rdev;
    long          st_size;
    long          st_blksize;
    long          st_blocks;
    unsigned long st_atime;
    unsigned long st_atime_nsec;
    unsigned long st_mtime;
    unsigned long st_mtime_nsec;
    unsigned long st_ctime;
    unsigned long st_ctime_nsec;
    long          __reserved[3];
};

#endif /* LINUX_COMPAT_H */
#define LINUX_SYS_sched_setscheduler 144
#define LINUX_SYS_sched_getparam 143
#define LINUX_SYS_sched_getscheduler 145

/**
 * @file linux_syscall_dispatch.c
 * @brief Linux Syscall Dispatcher for Exokernel LibOS
 *
 * Central dispatcher translating Linux x86_64 syscalls to exokernel operations.
 * Implements the System V AMD64 ABI for syscall conventions:
 *   - rax: syscall number
 *   - rdi, rsi, rdx, r10, r8, r9: arguments 1-6
 *   - Return value in rax
 *
 * References:
 * - https://man7.org/linux/man-pages/man2/syscalls.2.html
 * - https://eli.thegreenplace.net/2018/launching-linux-threads-and-processes-with-clone/
 */

#include "linux_syscall.h"
#include <errno.h>
#include <stdarg.h>
#include <sys/types.h>  /* for off_t */

/*
 * Forward declarations for syscall handlers
 */

/* Process/Thread */
extern long linux_sys_clone(unsigned long flags, void *stack, int *parent_tid,
                            int *child_tid, unsigned long tls);
extern long linux_sys_clone3(struct linux_clone_args *args, size_t size);
extern long linux_sys_fork(void);
extern long linux_sys_vfork(void);
extern long linux_sys_execve(const char *path, char *const argv[], char *const envp[]);
extern long linux_sys_execveat(int dirfd, const char *path, char *const argv[],
                               char *const envp[], int flags);
extern void linux_sys_exit(int status);
extern void linux_sys_exit_group(int status);
extern long linux_sys_wait4(int pid, int *status, int options, struct linux_rusage *rusage);
extern long linux_sys_waitid(int which, int pid, void *infop, int options, struct linux_rusage *rusage);
extern long linux_sys_getpid(void);
extern long linux_sys_gettid(void);
extern long linux_sys_getppid(void);
extern long linux_sys_getpgid(int pid);
extern long linux_sys_setpgid(int pid, int pgid);
extern long linux_sys_getsid(int pid);
extern long linux_sys_setsid(void);

/* Thread-related */
extern long linux_sys_set_tid_address(int *tidptr);
extern long linux_sys_set_robust_list(struct linux_robust_list_head *head, size_t len);
extern long linux_sys_get_robust_list(int pid, struct linux_robust_list_head **head, size_t *len);
extern long linux_sys_futex(int *uaddr, int op, int val, const struct linux_timespec *timeout,
                            int *uaddr2, int val3);

/* Memory */
extern long linux_sys_mmap(void *addr, size_t length, int prot, int flags, int fd, off_t offset);
extern long linux_sys_munmap(void *addr, size_t length);
extern long linux_sys_mprotect(void *addr, size_t len, int prot);
extern long linux_sys_brk(void *addr);
extern long linux_sys_mremap(void *old_addr, size_t old_size, size_t new_size,
                             int flags, void *new_addr);
extern long linux_sys_madvise(void *addr, size_t length, int advice);
extern long linux_sys_mlock(const void *addr, size_t len);
extern long linux_sys_munlock(const void *addr, size_t len);

/* File I/O */
extern long linux_sys_read(int fd, void *buf, size_t count);
extern long linux_sys_write(int fd, const void *buf, size_t count);
extern long linux_sys_open(const char *path, int flags, int mode);
extern long linux_sys_close(int fd);
extern long linux_sys_openat(int dirfd, const char *path, int flags, int mode);
extern long linux_sys_lseek(int fd, off_t offset, int whence);
extern long linux_sys_pread64(int fd, void *buf, size_t count, off_t offset);
extern long linux_sys_pwrite64(int fd, const void *buf, size_t count, off_t offset);
extern long linux_sys_readv(int fd, const struct linux_iovec *iov, int iovcnt);
extern long linux_sys_writev(int fd, const struct linux_iovec *iov, int iovcnt);

/* File Operations */
extern long linux_sys_stat(const char *path, struct linux_stat *buf);
extern long linux_sys_fstat(int fd, struct linux_stat *buf);
extern long linux_sys_lstat(const char *path, struct linux_stat *buf);
extern long linux_sys_newfstatat(int dirfd, const char *path, struct linux_stat *buf, int flags);
extern long linux_sys_statx(int dirfd, const char *path, int flags, unsigned int mask,
                            struct linux_statx *buf);
extern long linux_sys_access(const char *path, int mode);
extern long linux_sys_faccessat(int dirfd, const char *path, int mode, int flags);
extern long linux_sys_faccessat2(int dirfd, const char *path, int mode, int flags);

/* Directory Operations */
extern long linux_sys_mkdir(const char *path, int mode);
extern long linux_sys_mkdirat(int dirfd, const char *path, int mode);
extern long linux_sys_rmdir(const char *path);
extern long linux_sys_unlink(const char *path);
extern long linux_sys_unlinkat(int dirfd, const char *path, int flags);
extern long linux_sys_rename(const char *oldpath, const char *newpath);
extern long linux_sys_renameat(int olddirfd, const char *oldpath, int newdirfd, const char *newpath);
extern long linux_sys_renameat2(int olddirfd, const char *oldpath, int newdirfd,
                                const char *newpath, unsigned int flags);
extern long linux_sys_link(const char *oldpath, const char *newpath);
extern long linux_sys_linkat(int olddirfd, const char *oldpath, int newdirfd,
                             const char *newpath, int flags);
extern long linux_sys_symlink(const char *target, const char *linkpath);
extern long linux_sys_symlinkat(const char *target, int newdirfd, const char *linkpath);
extern long linux_sys_readlink(const char *path, char *buf, size_t bufsiz);
extern long linux_sys_readlinkat(int dirfd, const char *path, char *buf, size_t bufsiz);
extern long linux_sys_getdents64(int fd, void *dirp, size_t count);
extern long linux_sys_getcwd(char *buf, size_t size);
extern long linux_sys_chdir(const char *path);
extern long linux_sys_fchdir(int fd);

/* File Descriptor */
extern long linux_sys_dup(int oldfd);
extern long linux_sys_dup2(int oldfd, int newfd);
extern long linux_sys_dup3(int oldfd, int newfd, int flags);
extern long linux_sys_pipe(int pipefd[2]);
extern long linux_sys_pipe2(int pipefd[2], int flags);
extern long linux_sys_fcntl(int fd, int cmd, unsigned long arg);
extern long linux_sys_ioctl(int fd, unsigned long request, unsigned long arg);

/* File Permissions */
extern long linux_sys_chmod(const char *path, int mode);
extern long linux_sys_fchmod(int fd, int mode);
extern long linux_sys_fchmodat(int dirfd, const char *path, int mode, int flags);
extern long linux_sys_chown(const char *path, int owner, int group);
extern long linux_sys_fchown(int fd, int owner, int group);
extern long linux_sys_fchownat(int dirfd, const char *path, int owner, int group, int flags);
extern long linux_sys_lchown(const char *path, int owner, int group);
extern long linux_sys_umask(int mask);

/* Signals */
extern long linux_sys_rt_sigaction(int sig, const struct linux_sigaction *act,
                                   struct linux_sigaction *oact, size_t sigsetsize);
extern long linux_sys_rt_sigprocmask(int how, const uint64_t *set, uint64_t *oset, size_t sigsetsize);
extern long linux_sys_rt_sigreturn(void);
extern long linux_sys_rt_sigpending(uint64_t *set, size_t sigsetsize);
extern long linux_sys_rt_sigsuspend(const uint64_t *mask, size_t sigsetsize);
extern long linux_sys_rt_sigtimedwait(const uint64_t *set, void *info,
                                      const struct linux_timespec *timeout, size_t sigsetsize);
extern long linux_sys_kill(int pid, int sig);
extern long linux_sys_tkill(int tid, int sig);
extern long linux_sys_tgkill(int tgid, int tid, int sig);
extern long linux_sys_sigaltstack(const void *ss, void *old_ss);

/* Event I/O */
extern long linux_sys_epoll_create(int size);
extern long linux_sys_epoll_create1(int flags);
extern long linux_sys_epoll_ctl(int epfd, int op, int fd, struct linux_epoll_event *event);
extern long linux_sys_epoll_wait(int epfd, struct linux_epoll_event *events, int maxevents, int timeout);
extern long linux_sys_epoll_pwait(int epfd, struct linux_epoll_event *events, int maxevents,
                                  int timeout, const uint64_t *sigmask, size_t sigsetsize);
extern long linux_sys_epoll_pwait2(int epfd, struct linux_epoll_event *events, int maxevents,
                                   const struct linux_timespec *timeout, const uint64_t *sigmask,
                                   size_t sigsetsize);
extern long linux_sys_select(int nfds, void *readfds, void *writefds, void *exceptfds,
                             struct linux_timeval *timeout);
extern long linux_sys_pselect6(int nfds, void *readfds, void *writefds, void *exceptfds,
                               const struct linux_timespec *timeout, const void *sigmask);
extern long linux_sys_poll(void *fds, unsigned int nfds, int timeout);
extern long linux_sys_ppoll(void *fds, unsigned int nfds, const struct linux_timespec *tmo,
                            const uint64_t *sigmask, size_t sigsetsize);

/* Timer/Event FDs */
extern long linux_sys_timerfd_create(int clockid, int flags);
extern long linux_sys_timerfd_settime(int fd, int flags, const void *new_value, void *old_value);
extern long linux_sys_timerfd_gettime(int fd, void *curr_value);
extern long linux_sys_eventfd(unsigned int initval);
extern long linux_sys_eventfd2(unsigned int initval, int flags);
extern long linux_sys_signalfd(int fd, const uint64_t *mask, size_t sizemask);
extern long linux_sys_signalfd4(int fd, const uint64_t *mask, size_t sizemask, int flags);

/* Inotify */
extern long linux_sys_inotify_init(void);
extern long linux_sys_inotify_init1(int flags);
extern long linux_sys_inotify_add_watch(int fd, const char *pathname, uint32_t mask);
extern long linux_sys_inotify_rm_watch(int fd, int wd);

/* Sockets */
extern long linux_sys_socket(int domain, int type, int protocol);
extern long linux_sys_socketpair(int domain, int type, int protocol, int sv[2]);
extern long linux_sys_bind(int sockfd, const void *addr, int addrlen);
extern long linux_sys_listen(int sockfd, int backlog);
extern long linux_sys_accept(int sockfd, void *addr, int *addrlen);
extern long linux_sys_accept4(int sockfd, void *addr, int *addrlen, int flags);
extern long linux_sys_connect(int sockfd, const void *addr, int addrlen);
extern long linux_sys_getsockname(int sockfd, void *addr, int *addrlen);
extern long linux_sys_getpeername(int sockfd, void *addr, int *addrlen);
extern long linux_sys_sendto(int sockfd, const void *buf, size_t len, int flags,
                             const void *dest_addr, int addrlen);
extern long linux_sys_recvfrom(int sockfd, void *buf, size_t len, int flags,
                               void *src_addr, int *addrlen);
extern long linux_sys_sendmsg(int sockfd, const void *msg, int flags);
extern long linux_sys_recvmsg(int sockfd, void *msg, int flags);
extern long linux_sys_shutdown(int sockfd, int how);
extern long linux_sys_setsockopt(int sockfd, int level, int optname, const void *optval, int optlen);
extern long linux_sys_getsockopt(int sockfd, int level, int optname, void *optval, int *optlen);

/* Time */
extern long linux_sys_nanosleep(const struct linux_timespec *req, struct linux_timespec *rem);
extern long linux_sys_clock_gettime(int clockid, struct linux_timespec *tp);
extern long linux_sys_clock_settime(int clockid, const struct linux_timespec *tp);
extern long linux_sys_clock_getres(int clockid, struct linux_timespec *res);
extern long linux_sys_clock_nanosleep(int clockid, int flags, const struct linux_timespec *req,
                                      struct linux_timespec *rem);
extern long linux_sys_gettimeofday(struct linux_timeval *tv, void *tz);
extern long linux_sys_settimeofday(const struct linux_timeval *tv, const void *tz);
extern long linux_sys_time(long *tloc);
extern long linux_sys_times(void *buf);

/* User/Group IDs */
extern long linux_sys_getuid(void);
extern long linux_sys_getgid(void);
extern long linux_sys_geteuid(void);
extern long linux_sys_getegid(void);
extern long linux_sys_setuid(int uid);
extern long linux_sys_setgid(int gid);
extern long linux_sys_setreuid(int ruid, int euid);
extern long linux_sys_setregid(int rgid, int egid);
extern long linux_sys_getgroups(int size, int list[]);
extern long linux_sys_setgroups(int size, const int list[]);
extern long linux_sys_setresuid(int ruid, int euid, int suid);
extern long linux_sys_getresuid(int *ruid, int *euid, int *suid);
extern long linux_sys_setresgid(int rgid, int egid, int sgid);
extern long linux_sys_getresgid(int *rgid, int *egid, int *sgid);

/* Resource Limits */
extern long linux_sys_getrlimit(int resource, struct linux_rlimit *rlim);
extern long linux_sys_setrlimit(int resource, const struct linux_rlimit *rlim);
extern long linux_sys_prlimit64(int pid, int resource, const struct linux_rlimit *new_limit,
                                struct linux_rlimit *old_limit);
extern long linux_sys_getrusage(int who, struct linux_rusage *usage);

/* System Info */
extern long linux_sys_uname(struct linux_utsname *buf);
extern long linux_sys_sysinfo(struct linux_sysinfo *info);
extern long linux_sys_getcpu(unsigned int *cpu, unsigned int *node, void *tcache);

/* Miscellaneous */
extern long linux_sys_prctl(int option, unsigned long arg2, unsigned long arg3,
                            unsigned long arg4, unsigned long arg5);
extern long linux_sys_arch_prctl(int code, unsigned long addr);
extern long linux_sys_getrandom(void *buf, size_t buflen, unsigned int flags);
extern long linux_sys_memfd_create(const char *name, unsigned int flags);

/* Scheduling */
extern long linux_sys_sched_yield(void);
extern long linux_sys_sched_setscheduler(int pid, int policy, const void *param);
extern long linux_sys_sched_getscheduler(int pid);
extern long linux_sys_sched_setparam(int pid, const void *param);
extern long linux_sys_sched_getparam(int pid, void *param);
extern long linux_sys_sched_setaffinity(int pid, size_t cpusetsize, const void *mask);
extern long linux_sys_sched_getaffinity(int pid, size_t cpusetsize, void *mask);
extern long linux_sys_sched_get_priority_max(int policy);
extern long linux_sys_sched_get_priority_min(int policy);

/* Filesystem Sync */
extern long linux_sys_sync(void);
extern long linux_sys_syncfs(int fd);
extern long linux_sys_fsync(int fd);
extern long linux_sys_fdatasync(int fd);

/*
 * ============================================================================
 * Main Syscall Dispatcher
 * ============================================================================
 */

/**
 * linux_syscall - Main Linux syscall dispatch function
 * @sysno: System call number (from rax)
 * @a1-a6: Arguments (rdi, rsi, rdx, r10, r8, r9)
 *
 * Returns syscall result or negative errno on error.
 */
long linux_syscall(long sysno, long a1, long a2, long a3, long a4, long a5, long a6)
{
    switch (sysno) {
    /*
     * File I/O
     */
    case __NR_read:
        return linux_sys_read((int)a1, (void *)a2, (size_t)a3);
    case __NR_write:
        return linux_sys_write((int)a1, (const void *)a2, (size_t)a3);
    case __NR_open:
        return linux_sys_open((const char *)a1, (int)a2, (int)a3);
    case __NR_close:
        return linux_sys_close((int)a1);
    case __NR_openat:
        return linux_sys_openat((int)a1, (const char *)a2, (int)a3, (int)a4);
    case __NR_lseek:
        return linux_sys_lseek((int)a1, (off_t)a2, (int)a3);
    case __NR_pread64:
        return linux_sys_pread64((int)a1, (void *)a2, (size_t)a3, (off_t)a4);
    case __NR_pwrite64:
        return linux_sys_pwrite64((int)a1, (const void *)a2, (size_t)a3, (off_t)a4);
    case __NR_readv:
        return linux_sys_readv((int)a1, (const struct linux_iovec *)a2, (int)a3);
    case __NR_writev:
        return linux_sys_writev((int)a1, (const struct linux_iovec *)a2, (int)a3);

    /*
     * File Status
     */
    case __NR_stat:
        return linux_sys_stat((const char *)a1, (struct linux_stat *)a2);
    case __NR_fstat:
        return linux_sys_fstat((int)a1, (struct linux_stat *)a2);
    case __NR_lstat:
        return linux_sys_lstat((const char *)a1, (struct linux_stat *)a2);
    case __NR_newfstatat:
        return linux_sys_newfstatat((int)a1, (const char *)a2, (struct linux_stat *)a3, (int)a4);
    case __NR_statx:
        return linux_sys_statx((int)a1, (const char *)a2, (int)a3, (unsigned int)a4,
                               (struct linux_statx *)a5);
    case __NR_access:
        return linux_sys_access((const char *)a1, (int)a2);
    case __NR_faccessat:
        return linux_sys_faccessat((int)a1, (const char *)a2, (int)a3, (int)a4);
    case __NR_faccessat2:
        return linux_sys_faccessat2((int)a1, (const char *)a2, (int)a3, (int)a4);

    /*
     * Memory Management
     */
    case __NR_mmap:
        return linux_sys_mmap((void *)a1, (size_t)a2, (int)a3, (int)a4, (int)a5, (off_t)a6);
    case __NR_munmap:
        return linux_sys_munmap((void *)a1, (size_t)a2);
    case __NR_mprotect:
        return linux_sys_mprotect((void *)a1, (size_t)a2, (int)a3);
    case __NR_brk:
        return linux_sys_brk((void *)a1);
    case __NR_mremap:
        return linux_sys_mremap((void *)a1, (size_t)a2, (size_t)a3, (int)a4, (void *)a5);
    case __NR_madvise:
        return linux_sys_madvise((void *)a1, (size_t)a2, (int)a3);
    case __NR_mlock:
        return linux_sys_mlock((const void *)a1, (size_t)a2);
    case __NR_munlock:
        return linux_sys_munlock((const void *)a1, (size_t)a2);

    /*
     * Process/Thread Control
     */
    case __NR_clone:
        return linux_sys_clone((unsigned long)a1, (void *)a2, (int *)a3, (int *)a4, (unsigned long)a5);
    case __NR_clone3:
        return linux_sys_clone3((struct linux_clone_args *)a1, (size_t)a2);
    case __NR_fork:
        return linux_sys_fork();
    case __NR_vfork:
        return linux_sys_vfork();
    case __NR_execve:
        return linux_sys_execve((const char *)a1, (char *const *)a2, (char *const *)a3);
    case __NR_execveat:
        return linux_sys_execveat((int)a1, (const char *)a2, (char *const *)a3,
                                  (char *const *)a4, (int)a5);
    case __NR_exit:
        linux_sys_exit((int)a1);
        return 0;
    case __NR_exit_group:
        linux_sys_exit_group((int)a1);
        return 0;
    case __NR_wait4:
        return linux_sys_wait4((int)a1, (int *)a2, (int)a3, (struct linux_rusage *)a4);
    case __NR_waitid:
        return linux_sys_waitid((int)a1, (int)a2, (void *)a3, (int)a4, (struct linux_rusage *)a5);
    case __NR_getpid:
        return linux_sys_getpid();
    case __NR_gettid:
        return linux_sys_gettid();
    case __NR_getppid:
        return linux_sys_getppid();
    case __NR_getpgid:
        return linux_sys_getpgid((int)a1);
    case __NR_setpgid:
        return linux_sys_setpgid((int)a1, (int)a2);
    case __NR_getsid:
        return linux_sys_getsid((int)a1);
    case __NR_setsid:
        return linux_sys_setsid();
    case __NR_set_tid_address:
        return linux_sys_set_tid_address((int *)a1);
    case __NR_set_robust_list:
        return linux_sys_set_robust_list((struct linux_robust_list_head *)a1, (size_t)a2);
    case __NR_get_robust_list:
        return linux_sys_get_robust_list((int)a1, (struct linux_robust_list_head **)a2, (size_t *)a3);

    /*
     * Futex (Fast Userspace Mutex)
     */
    case __NR_futex:
        return linux_sys_futex((int *)a1, (int)a2, (int)a3,
                               (const struct linux_timespec *)a4, (int *)a5, (int)a6);

    /*
     * Signals
     */
    case __NR_rt_sigaction:
        return linux_sys_rt_sigaction((int)a1, (const struct linux_sigaction *)a2,
                                      (struct linux_sigaction *)a3, (size_t)a4);
    case __NR_rt_sigprocmask:
        return linux_sys_rt_sigprocmask((int)a1, (const uint64_t *)a2, (uint64_t *)a3, (size_t)a4);
    case __NR_rt_sigreturn:
        return linux_sys_rt_sigreturn();
    case __NR_rt_sigpending:
        return linux_sys_rt_sigpending((uint64_t *)a1, (size_t)a2);
    case __NR_rt_sigsuspend:
        return linux_sys_rt_sigsuspend((const uint64_t *)a1, (size_t)a2);
    case __NR_kill:
        return linux_sys_kill((int)a1, (int)a2);
    case __NR_tkill:
        return linux_sys_tkill((int)a1, (int)a2);
    case __NR_tgkill:
        return linux_sys_tgkill((int)a1, (int)a2, (int)a3);
    case __NR_sigaltstack:
        return linux_sys_sigaltstack((const void *)a1, (void *)a2);

    /*
     * Epoll
     */
    case __NR_epoll_create:
        return linux_sys_epoll_create((int)a1);
    case __NR_epoll_create1:
        return linux_sys_epoll_create1((int)a1);
    case __NR_epoll_ctl:
        return linux_sys_epoll_ctl((int)a1, (int)a2, (int)a3, (struct linux_epoll_event *)a4);
    case __NR_epoll_wait:
        return linux_sys_epoll_wait((int)a1, (struct linux_epoll_event *)a2, (int)a3, (int)a4);
    case __NR_epoll_pwait:
        return linux_sys_epoll_pwait((int)a1, (struct linux_epoll_event *)a2, (int)a3,
                                     (int)a4, (const uint64_t *)a5, (size_t)a6);

    /*
     * Select/Poll
     */
    case __NR_select:
        return linux_sys_select((int)a1, (void *)a2, (void *)a3, (void *)a4,
                                (struct linux_timeval *)a5);
    case __NR_poll:
        return linux_sys_poll((void *)a1, (unsigned int)a2, (int)a3);
    case __NR_pselect6:
        return linux_sys_pselect6((int)a1, (void *)a2, (void *)a3, (void *)a4,
                                  (const struct linux_timespec *)a5, (const void *)a6);
    case __NR_ppoll:
        return linux_sys_ppoll((void *)a1, (unsigned int)a2, (const struct linux_timespec *)a3,
                               (const uint64_t *)a4, (size_t)a5);

    /*
     * Timer/Event FDs
     */
    case __NR_timerfd_create:
        return linux_sys_timerfd_create((int)a1, (int)a2);
    case __NR_timerfd_settime:
        return linux_sys_timerfd_settime((int)a1, (int)a2, (const void *)a3, (void *)a4);
    case __NR_timerfd_gettime:
        return linux_sys_timerfd_gettime((int)a1, (void *)a2);
    case __NR_eventfd:
        return linux_sys_eventfd((unsigned int)a1);
    case __NR_eventfd2:
        return linux_sys_eventfd2((unsigned int)a1, (int)a2);
    case __NR_signalfd:
        return linux_sys_signalfd((int)a1, (const uint64_t *)a2, (size_t)a3);
    case __NR_signalfd4:
        return linux_sys_signalfd4((int)a1, (const uint64_t *)a2, (size_t)a3, (int)a4);

    /*
     * Inotify
     */
    case __NR_inotify_init:
        return linux_sys_inotify_init();
    case __NR_inotify_init1:
        return linux_sys_inotify_init1((int)a1);
    case __NR_inotify_add_watch:
        return linux_sys_inotify_add_watch((int)a1, (const char *)a2, (uint32_t)a3);
    case __NR_inotify_rm_watch:
        return linux_sys_inotify_rm_watch((int)a1, (int)a2);

    /*
     * Directory Operations
     */
    case __NR_mkdir:
        return linux_sys_mkdir((const char *)a1, (int)a2);
    case __NR_mkdirat:
        return linux_sys_mkdirat((int)a1, (const char *)a2, (int)a3);
    case __NR_rmdir:
        return linux_sys_rmdir((const char *)a1);
    case __NR_unlink:
        return linux_sys_unlink((const char *)a1);
    case __NR_unlinkat:
        return linux_sys_unlinkat((int)a1, (const char *)a2, (int)a3);
    case __NR_rename:
        return linux_sys_rename((const char *)a1, (const char *)a2);
    case __NR_renameat:
        return linux_sys_renameat((int)a1, (const char *)a2, (int)a3, (const char *)a4);
    case __NR_renameat2:
        return linux_sys_renameat2((int)a1, (const char *)a2, (int)a3, (const char *)a4, (unsigned int)a5);
    case __NR_link:
        return linux_sys_link((const char *)a1, (const char *)a2);
    case __NR_linkat:
        return linux_sys_linkat((int)a1, (const char *)a2, (int)a3, (const char *)a4, (int)a5);
    case __NR_symlink:
        return linux_sys_symlink((const char *)a1, (const char *)a2);
    case __NR_symlinkat:
        return linux_sys_symlinkat((const char *)a1, (int)a2, (const char *)a3);
    case __NR_readlink:
        return linux_sys_readlink((const char *)a1, (char *)a2, (size_t)a3);
    case __NR_readlinkat:
        return linux_sys_readlinkat((int)a1, (const char *)a2, (char *)a3, (size_t)a4);
    case __NR_getdents64:
        return linux_sys_getdents64((int)a1, (void *)a2, (size_t)a3);
    case __NR_getcwd:
        return linux_sys_getcwd((char *)a1, (size_t)a2);
    case __NR_chdir:
        return linux_sys_chdir((const char *)a1);
    case __NR_fchdir:
        return linux_sys_fchdir((int)a1);

    /*
     * File Descriptor Operations
     */
    case __NR_dup:
        return linux_sys_dup((int)a1);
    case __NR_dup2:
        return linux_sys_dup2((int)a1, (int)a2);
    case __NR_dup3:
        return linux_sys_dup3((int)a1, (int)a2, (int)a3);
    case __NR_pipe:
        return linux_sys_pipe((int *)a1);
    case __NR_pipe2:
        return linux_sys_pipe2((int *)a1, (int)a2);
    case __NR_fcntl:
        return linux_sys_fcntl((int)a1, (int)a2, (unsigned long)a3);
    case __NR_ioctl:
        return linux_sys_ioctl((int)a1, (unsigned long)a2, (unsigned long)a3);

    /*
     * File Permissions
     */
    case __NR_chmod:
        return linux_sys_chmod((const char *)a1, (int)a2);
    case __NR_fchmod:
        return linux_sys_fchmod((int)a1, (int)a2);
    case __NR_fchmodat:
        return linux_sys_fchmodat((int)a1, (const char *)a2, (int)a3, (int)a4);
    case __NR_chown:
        return linux_sys_chown((const char *)a1, (int)a2, (int)a3);
    case __NR_fchown:
        return linux_sys_fchown((int)a1, (int)a2, (int)a3);
    case __NR_fchownat:
        return linux_sys_fchownat((int)a1, (const char *)a2, (int)a3, (int)a4, (int)a5);
    case __NR_lchown:
        return linux_sys_lchown((const char *)a1, (int)a2, (int)a3);
    case __NR_umask:
        return linux_sys_umask((int)a1);

    /*
     * Sockets
     */
    case __NR_socket:
        return linux_sys_socket((int)a1, (int)a2, (int)a3);
    case __NR_socketpair:
        return linux_sys_socketpair((int)a1, (int)a2, (int)a3, (int *)a4);
    case __NR_bind:
        return linux_sys_bind((int)a1, (const void *)a2, (int)a3);
    case __NR_listen:
        return linux_sys_listen((int)a1, (int)a2);
    case __NR_accept:
        return linux_sys_accept((int)a1, (void *)a2, (int *)a3);
    case __NR_accept4:
        return linux_sys_accept4((int)a1, (void *)a2, (int *)a3, (int)a4);
    case __NR_connect:
        return linux_sys_connect((int)a1, (const void *)a2, (int)a3);
    case __NR_getsockname:
        return linux_sys_getsockname((int)a1, (void *)a2, (int *)a3);
    case __NR_getpeername:
        return linux_sys_getpeername((int)a1, (void *)a2, (int *)a3);
    case __NR_sendto:
        return linux_sys_sendto((int)a1, (const void *)a2, (size_t)a3, (int)a4,
                                (const void *)a5, (int)a6);
    case __NR_recvfrom:
        return linux_sys_recvfrom((int)a1, (void *)a2, (size_t)a3, (int)a4,
                                  (void *)a5, (int *)a6);
    case __NR_sendmsg:
        return linux_sys_sendmsg((int)a1, (const void *)a2, (int)a3);
    case __NR_recvmsg:
        return linux_sys_recvmsg((int)a1, (void *)a2, (int)a3);
    case __NR_shutdown:
        return linux_sys_shutdown((int)a1, (int)a2);
    case __NR_setsockopt:
        return linux_sys_setsockopt((int)a1, (int)a2, (int)a3, (const void *)a4, (int)a5);
    case __NR_getsockopt:
        return linux_sys_getsockopt((int)a1, (int)a2, (int)a3, (void *)a4, (int *)a5);

    /*
     * Time
     */
    case __NR_nanosleep:
        return linux_sys_nanosleep((const struct linux_timespec *)a1, (struct linux_timespec *)a2);
    case __NR_clock_gettime:
        return linux_sys_clock_gettime((int)a1, (struct linux_timespec *)a2);
    case __NR_clock_settime:
        return linux_sys_clock_settime((int)a1, (const struct linux_timespec *)a2);
    case __NR_clock_getres:
        return linux_sys_clock_getres((int)a1, (struct linux_timespec *)a2);
    case __NR_clock_nanosleep:
        return linux_sys_clock_nanosleep((int)a1, (int)a2, (const struct linux_timespec *)a3,
                                         (struct linux_timespec *)a4);
    case __NR_gettimeofday:
        return linux_sys_gettimeofday((struct linux_timeval *)a1, (void *)a2);
    case __NR_time:
        return linux_sys_time((long *)a1);
    case __NR_times:
        return linux_sys_times((void *)a1);

    /*
     * User/Group IDs
     */
    case __NR_getuid:
        return linux_sys_getuid();
    case __NR_getgid:
        return linux_sys_getgid();
    case __NR_geteuid:
        return linux_sys_geteuid();
    case __NR_getegid:
        return linux_sys_getegid();
    case __NR_setuid:
        return linux_sys_setuid((int)a1);
    case __NR_setgid:
        return linux_sys_setgid((int)a1);

    /*
     * Resource Limits
     */
    case __NR_getrlimit:
        return linux_sys_getrlimit((int)a1, (struct linux_rlimit *)a2);
    case __NR_setrlimit:
        return linux_sys_setrlimit((int)a1, (const struct linux_rlimit *)a2);
    case __NR_prlimit64:
        return linux_sys_prlimit64((int)a1, (int)a2, (const struct linux_rlimit *)a3,
                                   (struct linux_rlimit *)a4);
    case __NR_getrusage:
        return linux_sys_getrusage((int)a1, (struct linux_rusage *)a2);

    /*
     * System Info
     */
    case __NR_uname:
        return linux_sys_uname((struct linux_utsname *)a1);
    case __NR_sysinfo:
        return linux_sys_sysinfo((struct linux_sysinfo *)a1);
    case __NR_getcpu:
        return linux_sys_getcpu((unsigned int *)a1, (unsigned int *)a2, (void *)a3);

    /*
     * Miscellaneous
     */
    case __NR_prctl:
        return linux_sys_prctl((int)a1, (unsigned long)a2, (unsigned long)a3,
                               (unsigned long)a4, (unsigned long)a5);
    case __NR_arch_prctl:
        return linux_sys_arch_prctl((int)a1, (unsigned long)a2);
    case __NR_getrandom:
        return linux_sys_getrandom((void *)a1, (size_t)a2, (unsigned int)a3);
    case __NR_memfd_create:
        return linux_sys_memfd_create((const char *)a1, (unsigned int)a2);

    /*
     * Scheduling
     */
    case __NR_sched_yield:
        return linux_sys_sched_yield();
    case __NR_sched_setscheduler:
        return linux_sys_sched_setscheduler((int)a1, (int)a2, (const void *)a3);
    case __NR_sched_getscheduler:
        return linux_sys_sched_getscheduler((int)a1);
    case __NR_sched_setparam:
        return linux_sys_sched_setparam((int)a1, (const void *)a2);
    case __NR_sched_getparam:
        return linux_sys_sched_getparam((int)a1, (void *)a2);
    case __NR_sched_setaffinity:
        return linux_sys_sched_setaffinity((int)a1, (size_t)a2, (const void *)a3);
    case __NR_sched_getaffinity:
        return linux_sys_sched_getaffinity((int)a1, (size_t)a2, (void *)a3);
    case __NR_sched_get_priority_max:
        return linux_sys_sched_get_priority_max((int)a1);
    case __NR_sched_get_priority_min:
        return linux_sys_sched_get_priority_min((int)a1);

    /*
     * Filesystem Sync
     */
    case __NR_sync:
        return linux_sys_sync();
    case __NR_syncfs:
        return linux_sys_syncfs((int)a1);
    case __NR_fsync:
        return linux_sys_fsync((int)a1);
    case __NR_fdatasync:
        return linux_sys_fdatasync((int)a1);

    /*
     * File Truncation
     */
    case __NR_truncate:
        return -ENOSYS;  /* TODO */
    case __NR_ftruncate:
        return -ENOSYS;  /* TODO */

    default:
        return -ENOSYS;
    }
}

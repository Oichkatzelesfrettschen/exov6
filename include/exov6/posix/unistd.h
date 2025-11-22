/* unistd.h - POSIX-2024 Standard Symbolic Constants and Types */
#ifndef _UNISTD_H
#define _UNISTD_H

#include <sys/types.h>
#include <stddef.h>

#ifdef __cplusplus
extern "C" {
#endif

/* POSIX-2024 version information */
#define _POSIX_VERSION          200809L
#define _POSIX2_VERSION         200809L
#define _XOPEN_VERSION          700

/* POSIX feature test macros */
#define _POSIX_ADVISORY_INFO                200809L
#define _POSIX_ASYNCHRONOUS_IO              200809L
#define _POSIX_BARRIERS                     200809L
#define _POSIX_CHOWN_RESTRICTED             1
#define _POSIX_CLOCK_SELECTION              200809L
#define _POSIX_CPUTIME                      200809L
#define _POSIX_FSYNC                        200809L
#define _POSIX_IPV6                         200809L
#define _POSIX_JOB_CONTROL                  1
#define _POSIX_MAPPED_FILES                 200809L
#define _POSIX_MEMLOCK                      200809L
#define _POSIX_MEMLOCK_RANGE                200809L
#define _POSIX_MEMORY_PROTECTION            200809L
#define _POSIX_MESSAGE_PASSING              200809L
#define _POSIX_MONOTONIC_CLOCK              200809L
#define _POSIX_NO_TRUNC                     1
#define _POSIX_PRIORITIZED_IO               200809L
#define _POSIX_PRIORITY_SCHEDULING          200809L
#define _POSIX_RAW_SOCKETS                  200809L
#define _POSIX_READER_WRITER_LOCKS          200809L
#define _POSIX_REALTIME_SIGNALS             200809L
#define _POSIX_REGEXP                       1
#define _POSIX_SAVED_IDS                    1
#define _POSIX_SEMAPHORES                   200809L
#define _POSIX_SHARED_MEMORY_OBJECTS        200809L
#define _POSIX_SHELL                        1
#define _POSIX_SPAWN                        200809L
#define _POSIX_SPIN_LOCKS                   200809L
#define _POSIX_SPORADIC_SERVER              -1
#define _POSIX_SYNCHRONIZED_IO              200809L
#define _POSIX_THREAD_ATTR_STACKADDR        200809L
#define _POSIX_THREAD_ATTR_STACKSIZE        200809L
#define _POSIX_THREAD_CPUTIME               200809L
#define _POSIX_THREAD_PRIO_INHERIT          200809L
#define _POSIX_THREAD_PRIO_PROTECT          200809L
#define _POSIX_THREAD_PRIORITY_SCHEDULING   200809L
#define _POSIX_THREAD_PROCESS_SHARED        200809L
#define _POSIX_THREAD_ROBUST_PRIO_INHERIT   200809L
#define _POSIX_THREAD_ROBUST_PRIO_PROTECT   200809L
#define _POSIX_THREAD_SAFE_FUNCTIONS        200809L
#define _POSIX_THREAD_SPORADIC_SERVER       -1
#define _POSIX_THREADS                      200809L
#define _POSIX_TIMEOUTS                     200809L
#define _POSIX_TIMERS                       200809L
#define _POSIX_TRACE                        -1
#define _POSIX_TRACE_EVENT_FILTER           -1
#define _POSIX_TRACE_INHERIT                -1
#define _POSIX_TRACE_LOG                    -1
#define _POSIX_TYPED_MEMORY_OBJECTS         -1
#define _POSIX_VDISABLE                     '\0'

/* Standard file descriptors */
#define STDIN_FILENO    0
#define STDOUT_FILENO   1
#define STDERR_FILENO   2

/* Symbolic constants for pathconf() */
#define _PC_LINK_MAX            0
#define _PC_MAX_CANON           1
#define _PC_MAX_INPUT           2
#define _PC_NAME_MAX            3
#define _PC_PATH_MAX            4
#define _PC_PIPE_BUF            5
#define _PC_CHOWN_RESTRICTED    6
#define _PC_NO_TRUNC            7
#define _PC_VDISABLE            8
#define _PC_ASYNC_IO            9
#define _PC_PRIO_IO             10
#define _PC_SYNC_IO             11
#define _PC_ALLOC_SIZE_MIN      12
#define _PC_REC_INCR_XFER_SIZE  13
#define _PC_REC_MAX_XFER_SIZE   14
#define _PC_REC_MIN_XFER_SIZE   15
#define _PC_REC_XFER_ALIGN      16
#define _PC_SYMLINK_MAX         17
#define _PC_2_SYMLINKS          18

/* Symbolic constants for sysconf() */
#define _SC_ARG_MAX                 0
#define _SC_CHILD_MAX               1
#define _SC_CLK_TCK                 2
#define _SC_NGROUPS_MAX             3
#define _SC_OPEN_MAX                4
#define _SC_STREAM_MAX              5
#define _SC_TZNAME_MAX              6
#define _SC_JOB_CONTROL             7
#define _SC_SAVED_IDS               8
#define _SC_REALTIME_SIGNALS        9
#define _SC_PRIORITY_SCHEDULING     10
#define _SC_TIMERS                  11
#define _SC_ASYNCHRONOUS_IO         12
#define _SC_PRIORITIZED_IO          13
#define _SC_SYNCHRONIZED_IO         14
#define _SC_FSYNC                   15
#define _SC_MAPPED_FILES            16
#define _SC_MEMLOCK                 17
#define _SC_MEMLOCK_RANGE           18
#define _SC_MEMORY_PROTECTION       19
#define _SC_MESSAGE_PASSING         20
#define _SC_SEMAPHORES              21
#define _SC_SHARED_MEMORY_OBJECTS   22
#define _SC_AIO_LISTIO_MAX          23
#define _SC_AIO_MAX                 24
#define _SC_AIO_PRIO_DELTA_MAX      25
#define _SC_DELAYTIMER_MAX          26
#define _SC_MQ_OPEN_MAX             27
#define _SC_MQ_PRIO_MAX             28
#define _SC_VERSION                 29
#define _SC_PAGESIZE                30
#define _SC_PAGE_SIZE               _SC_PAGESIZE
#define _SC_RTSIG_MAX               31
#define _SC_SEM_NSEMS_MAX           32
#define _SC_SEM_VALUE_MAX           33
#define _SC_SIGQUEUE_MAX            34
#define _SC_TIMER_MAX               35
#define _SC_BC_BASE_MAX             36
#define _SC_BC_DIM_MAX              37
#define _SC_BC_SCALE_MAX            38
#define _SC_BC_STRING_MAX           39
#define _SC_COLL_WEIGHTS_MAX        40
#define _SC_EXPR_NEST_MAX           41
#define _SC_LINE_MAX                42
#define _SC_RE_DUP_MAX              43
#define _SC_2_VERSION               44
#define _SC_2_C_BIND                45
#define _SC_2_C_DEV                 46
#define _SC_2_FORT_DEV              47
#define _SC_2_FORT_RUN              48
#define _SC_2_SW_DEV                49
#define _SC_2_LOCALEDEF             50
#define _SC_PHYS_PAGES              51
#define _SC_AVPHYS_PAGES            52
#define _SC_NPROCESSORS_CONF        53
#define _SC_NPROCESSORS_ONLN        54

/* Constants for lseek() */
#ifndef SEEK_SET
#define SEEK_SET    0   /* Set file offset to offset */
#define SEEK_CUR    1   /* Set file offset to current plus offset */
#define SEEK_END    2   /* Set file offset to EOF plus offset */
#endif

/* Constants for access() */
#define F_OK    0   /* Test for existence */
#define X_OK    1   /* Test for execute permission */
#define W_OK    2   /* Test for write permission */
#define R_OK    4   /* Test for read permission */

/* Constants for lockf() */
#define F_LOCK      1   /* Exclusive lock */
#define F_TLOCK     2   /* Test and lock */
#define F_ULOCK     3   /* Unlock */
#define F_TEST      4   /* Test for lock */

/* NULL pointer */
#ifndef NULL
#define NULL ((void *)0)
#endif

/* Process functions */
pid_t   fork(void);
pid_t   vfork(void);
int     execl(const char *path, const char *arg, ...);
int     execlp(const char *file, const char *arg, ...);
int     execle(const char *path, const char *arg, ...);
int     execv(const char *path, char *const argv[]);
int     execvp(const char *file, char *const argv[]);
int     execve(const char *path, char *const argv[], char *const envp[]);
void    _exit(int status) __attribute__((noreturn));
pid_t   getpid(void);
pid_t   getppid(void);
pid_t   getpgrp(void);
pid_t   getsid(pid_t pid);
pid_t   setsid(void);
int     setpgid(pid_t pid, pid_t pgid);

/* User and group functions */
uid_t   getuid(void);
uid_t   geteuid(void);
gid_t   getgid(void);
gid_t   getegid(void);
int     setuid(uid_t uid);
int     seteuid(uid_t euid);
int     setgid(gid_t gid);
int     setegid(gid_t egid);
int     getgroups(int gidsetsize, gid_t grouplist[]);
int     setgroups(size_t size, const gid_t *list);
char   *getlogin(void);
int     getlogin_r(char *name, size_t namesize);

/* File access constants for access() */
#define R_OK    4       /* Test for read permission */
#define W_OK    2       /* Test for write permission */  
#define X_OK    1       /* Test for execute permission */
#define F_OK    0       /* Test for existence */

/* File operations */
int     access(const char *path, int amode);
int     faccessat(int fd, const char *path, int amode, int flag);
int     chdir(const char *path);
int     fchdir(int fd);
char   *getcwd(char *buf, size_t size);
int     chown(const char *path, uid_t owner, gid_t group);
int     fchown(int fd, uid_t owner, gid_t group);
int     lchown(const char *path, uid_t owner, gid_t group);
int     fchownat(int fd, const char *path, uid_t owner, gid_t group, int flag);
int     link(const char *path1, const char *path2);
int     linkat(int fd1, const char *path1, int fd2, const char *path2, int flag);
int     unlink(const char *path);
int     unlinkat(int fd, const char *path, int flag);
int     rmdir(const char *path);
ssize_t readlink(const char *path, char *buf, size_t bufsize);
ssize_t readlinkat(int fd, const char *path, char *buf, size_t bufsize);
int     symlink(const char *path1, const char *path2);
int     symlinkat(const char *path1, int fd, const char *path2);

/* I/O functions */
ssize_t read(int fd, void *buf, size_t count);
ssize_t write(int fd, const void *buf, size_t count);
ssize_t pread(int fd, void *buf, size_t count, off_t offset);
ssize_t pwrite(int fd, const void *buf, size_t count, off_t offset);
int     close(int fd);
int     dup(int oldfd);
int     dup2(int oldfd, int newfd);
int     pipe(int pipefd[2]);
off_t   lseek(int fd, off_t offset, int whence);
int     fsync(int fd);
int     fdatasync(int fd);
int     sync(void);
unsigned int alarm(unsigned int seconds);
unsigned int sleep(unsigned int seconds);
int     usleep(useconds_t usec);
int     pause(void);

/* Terminal functions */
int     isatty(int fd);
char   *ttyname(int fd);
int     ttyname_r(int fd, char *buf, size_t buflen);

/* Hostname functions */
int     gethostname(char *name, size_t len);
int     sethostname(const char *name, size_t len);

/* Configuration functions */
long    sysconf(int name);
long    pathconf(const char *path, int name);
long    fpathconf(int fd, int name);

/* Obsolescent functions */
int     brk(void *addr);
void   *sbrk(intptr_t increment);
int     getpagesize(void);
int     getdtablesize(void);
char   *getpass(const char *prompt);

/* File locking */
int     lockf(int fd, int cmd, off_t len);

/* Process groups */
int     setpgrp(void);

/* Environment */
extern char **environ;
int     clearenv(void);

/* Deprecated but may be used */
pid_t   vhangup(void);

#ifdef __cplusplus
}
#endif

#endif /* _UNISTD_H */
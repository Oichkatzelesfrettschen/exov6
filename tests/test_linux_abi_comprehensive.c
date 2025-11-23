/**
 * @file test_linux_abi_comprehensive.c
 * @brief Comprehensive test suite for Linux ABI compatibility layer
 *
 * Tests all implemented Linux syscalls and verifies correct behavior
 * for the exokernel's Linux ABI emulation layer.
 */

#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <stdint.h>
#include <stdbool.h>

/* Include Linux ABI headers */
#include "../libos/linux/linux_syscall.h"

/*============================================================================
 * Test Framework
 *============================================================================*/

static int tests_run = 0;
static int tests_passed = 0;
static int tests_failed = 0;

#define TEST_ASSERT(cond, msg) do { \
    tests_run++; \
    if (cond) { \
        tests_passed++; \
        printf("  [PASS] %s\n", msg); \
    } else { \
        tests_failed++; \
        printf("  [FAIL] %s\n", msg); \
    } \
} while (0)

#define TEST_ASSERT_EQ(a, b, msg) TEST_ASSERT((a) == (b), msg)
#define TEST_ASSERT_NE(a, b, msg) TEST_ASSERT((a) != (b), msg)
#define TEST_ASSERT_GE(a, b, msg) TEST_ASSERT((a) >= (b), msg)
#define TEST_ASSERT_LT(a, b, msg) TEST_ASSERT((a) < (b), msg)

#define TEST_GROUP(name) printf("\n=== %s ===\n", name)

/*============================================================================
 * Mock External Functions (for testing without full kernel)
 *============================================================================*/

/* Mock exokernel primitives */
void *exo_alloc_pages(size_t count)
{
    return calloc(count, 4096);
}

void exo_free_pages(void *addr, size_t count)
{
    (void)count;
    free(addr);
}

int exo_protect_pages(void *addr, size_t count, int prot)
{
    (void)addr;
    (void)count;
    (void)prot;
    return 0;
}

void *exo_physical_alloc(size_t size)
{
    return malloc(size);
}

int exo_open(const char *path, int flags, int mode)
{
    (void)flags;
    (void)mode;
    /* Mock implementation */
    if (path && path[0] == '/') {
        static int next_fd = 10;
        return next_fd++;
    }
    return -1;
}

int exo_close(int fd)
{
    (void)fd;
    return 0;
}

ssize_t exo_read(int fd, void *buf, size_t count)
{
    (void)fd;
    memset(buf, 'X', count < 10 ? count : 10);
    return count < 10 ? count : 10;
}

ssize_t exo_write(int fd, const void *buf, size_t count)
{
    (void)fd;
    (void)buf;
    return count;
}

off_t exo_seek(int fd, off_t offset, int whence)
{
    (void)fd;
    (void)whence;
    return offset;
}

int exo_stat(const char *path, void *stat_buf)
{
    (void)path;
    struct linux_stat *st = stat_buf;
    st->st_size = 1024;
    st->st_mode = 0644;
    return 0;
}

int exo_fstat(int fd, void *stat_buf)
{
    (void)fd;
    struct linux_stat *st = stat_buf;
    st->st_size = 512;
    st->st_mode = 0644;
    return 0;
}

int exo_ioctl(int fd, unsigned long request, void *arg)
{
    (void)fd;
    (void)request;
    (void)arg;
    return 0;
}

int exo_thread_yield(void)
{
    return 0;
}

uint64_t exo_get_time_ns(void)
{
    static uint64_t time_counter = 1000000000ULL;
    return time_counter++;
}

/*============================================================================
 * Forward Declarations (syscall implementations)
 *============================================================================*/

/* Memory syscalls */
extern long linux_sys_mmap(unsigned long addr, unsigned long length,
                           unsigned long prot, unsigned long flags,
                           long fd, unsigned long offset);
extern long linux_sys_munmap(unsigned long addr, unsigned long length);
extern long linux_sys_mprotect(unsigned long addr, unsigned long length,
                               unsigned long prot);
extern long linux_sys_brk(unsigned long brk);
extern long linux_sys_mremap(unsigned long old_addr, unsigned long old_size,
                             unsigned long new_size, unsigned long flags,
                             unsigned long new_addr);
extern long linux_sys_madvise(unsigned long addr, unsigned long length, int advice);
extern long linux_sys_mlock(unsigned long addr, unsigned long length);
extern long linux_sys_munlock(unsigned long addr, unsigned long length);
extern long linux_sys_mlockall(int flags);
extern long linux_sys_munlockall(void);

/* File syscalls */
extern long linux_sys_openat(int dirfd, const char *pathname, int flags, int mode);
extern long linux_sys_open(const char *pathname, int flags, int mode);
extern long linux_sys_close(int fd);
extern long linux_sys_read(int fd, void *buf, size_t count);
extern long linux_sys_write(int fd, const void *buf, size_t count);
extern long linux_sys_lseek(int fd, off_t offset, int whence);
extern long linux_sys_pread64(int fd, void *buf, size_t count, off_t offset);
extern long linux_sys_pwrite64(int fd, const void *buf, size_t count, off_t offset);
extern long linux_sys_dup(int oldfd);
extern long linux_sys_dup2(int oldfd, int newfd);
extern long linux_sys_dup3(int oldfd, int newfd, int flags);
extern long linux_sys_fcntl(int fd, int cmd, unsigned long arg);
extern long linux_sys_fstat(int fd, struct linux_stat *statbuf);
extern long linux_sys_stat(const char *pathname, struct linux_stat *statbuf);
extern long linux_sys_pipe2(int pipefd[2], int flags);

/* Process syscalls */
extern long linux_sys_getpid(void);
extern long linux_sys_gettid(void);
extern long linux_sys_getppid(void);
extern long linux_sys_getpgid(int pid);
extern long linux_sys_getsid(int pid);
extern long linux_sys_set_tid_address(int *tidptr);

/* Signal syscalls */
extern long linux_sys_rt_sigaction(int signo, const struct linux_sigaction *act,
                                   struct linux_sigaction *oldact, size_t sigsetsize);
extern long linux_sys_rt_sigprocmask(int how, const void *set,
                                     void *oldset, size_t sigsetsize);
extern long linux_sys_kill(int pid, int signo);
extern long linux_sys_alarm(unsigned int seconds);

/* Epoll syscalls */
extern long linux_sys_epoll_create(int size);
extern long linux_sys_epoll_create1(int flags);
extern long linux_sys_epoll_ctl(int epfd, int op, int fd,
                                struct linux_epoll_event *event);
extern long linux_sys_epoll_wait(int epfd, struct linux_epoll_event *events,
                                 int maxevents, int timeout);

/* Futex syscalls */
extern long linux_sys_futex(uint32_t *uaddr, int op, uint32_t val,
                            const struct linux_timespec *timeout,
                            uint32_t *uaddr2, uint32_t val3);

/*============================================================================
 * Memory Syscall Tests
 *============================================================================*/

static void test_mmap_basic(void)
{
    TEST_GROUP("mmap basic tests");

    /* Anonymous mapping */
    long addr = linux_sys_mmap(0, 4096, LINUX_PROT_READ | LINUX_PROT_WRITE,
                               LINUX_MAP_PRIVATE | LINUX_MAP_ANONYMOUS, -1, 0);
    TEST_ASSERT(addr > 0, "mmap anonymous should return valid address");

    /* Check we can write to it */
    if (addr > 0) {
        *((int *)addr) = 42;
        TEST_ASSERT_EQ(*((int *)addr), 42, "mmap memory should be writable");

        /* Unmap it */
        long ret = linux_sys_munmap(addr, 4096);
        TEST_ASSERT_EQ(ret, 0, "munmap should succeed");
    }
}

static void test_mmap_fixed(void)
{
    TEST_GROUP("mmap MAP_FIXED tests");

    uintptr_t fixed_addr = 0x100000000UL;
    long addr = linux_sys_mmap(fixed_addr, 4096,
                               LINUX_PROT_READ | LINUX_PROT_WRITE,
                               LINUX_MAP_PRIVATE | LINUX_MAP_ANONYMOUS | LINUX_MAP_FIXED,
                               -1, 0);
    TEST_ASSERT_EQ((uintptr_t)addr, fixed_addr, "MAP_FIXED should return exact address");

    if (addr > 0) {
        linux_sys_munmap(addr, 4096);
    }
}

static void test_mprotect(void)
{
    TEST_GROUP("mprotect tests");

    long addr = linux_sys_mmap(0, 4096, LINUX_PROT_READ | LINUX_PROT_WRITE,
                               LINUX_MAP_PRIVATE | LINUX_MAP_ANONYMOUS, -1, 0);
    TEST_ASSERT(addr > 0, "mmap for mprotect test");

    if (addr > 0) {
        /* Change to read-only */
        long ret = linux_sys_mprotect(addr, 4096, LINUX_PROT_READ);
        TEST_ASSERT_EQ(ret, 0, "mprotect to read-only should succeed");

        /* Change back */
        ret = linux_sys_mprotect(addr, 4096, LINUX_PROT_READ | LINUX_PROT_WRITE);
        TEST_ASSERT_EQ(ret, 0, "mprotect to read-write should succeed");

        linux_sys_munmap(addr, 4096);
    }
}

static void test_brk(void)
{
    TEST_GROUP("brk tests");

    /* Get current break */
    long current = linux_sys_brk(0);
    TEST_ASSERT(current > 0, "brk(0) should return current break");

    /* Extend break */
    long new_brk = linux_sys_brk(current + 4096);
    TEST_ASSERT_GE(new_brk, current + 4096, "brk should extend");

    /* Shrink break */
    long shrunk = linux_sys_brk(current);
    TEST_ASSERT_EQ(shrunk, current, "brk should allow shrinking");
}

static void test_mremap(void)
{
    TEST_GROUP("mremap tests");

    long addr = linux_sys_mmap(0, 4096, LINUX_PROT_READ | LINUX_PROT_WRITE,
                               LINUX_MAP_PRIVATE | LINUX_MAP_ANONYMOUS, -1, 0);
    TEST_ASSERT(addr > 0, "mmap for mremap test");

    if (addr > 0) {
        /* Write some data */
        *((int *)addr) = 12345;

        /* Expand the mapping */
        long new_addr = linux_sys_mremap(addr, 4096, 8192, LINUX_MREMAP_MAYMOVE, 0);
        TEST_ASSERT(new_addr > 0, "mremap should succeed");

        /* Data should be preserved */
        if (new_addr > 0) {
            TEST_ASSERT_EQ(*((int *)new_addr), 12345, "mremap should preserve data");
            linux_sys_munmap(new_addr, 8192);
        }
    }
}

static void test_madvise(void)
{
    TEST_GROUP("madvise tests");

    long addr = linux_sys_mmap(0, 8192, LINUX_PROT_READ | LINUX_PROT_WRITE,
                               LINUX_MAP_PRIVATE | LINUX_MAP_ANONYMOUS, -1, 0);
    TEST_ASSERT(addr > 0, "mmap for madvise test");

    if (addr > 0) {
        /* Sequential access hint */
        long ret = linux_sys_madvise(addr, 8192, LINUX_MADV_SEQUENTIAL);
        TEST_ASSERT_EQ(ret, 0, "madvise SEQUENTIAL should succeed");

        /* Random access hint */
        ret = linux_sys_madvise(addr, 8192, LINUX_MADV_RANDOM);
        TEST_ASSERT_EQ(ret, 0, "madvise RANDOM should succeed");

        /* Don't need */
        ret = linux_sys_madvise(addr, 8192, LINUX_MADV_DONTNEED);
        TEST_ASSERT_EQ(ret, 0, "madvise DONTNEED should succeed");

        linux_sys_munmap(addr, 8192);
    }
}

static void test_mlock(void)
{
    TEST_GROUP("mlock tests");

    long addr = linux_sys_mmap(0, 4096, LINUX_PROT_READ | LINUX_PROT_WRITE,
                               LINUX_MAP_PRIVATE | LINUX_MAP_ANONYMOUS, -1, 0);
    TEST_ASSERT(addr > 0, "mmap for mlock test");

    if (addr > 0) {
        long ret = linux_sys_mlock(addr, 4096);
        TEST_ASSERT_EQ(ret, 0, "mlock should succeed");

        ret = linux_sys_munlock(addr, 4096);
        TEST_ASSERT_EQ(ret, 0, "munlock should succeed");

        linux_sys_munmap(addr, 4096);
    }

    /* Test mlockall */
    long ret = linux_sys_mlockall(LINUX_MCL_CURRENT);
    TEST_ASSERT_EQ(ret, 0, "mlockall should succeed");

    ret = linux_sys_munlockall();
    TEST_ASSERT_EQ(ret, 0, "munlockall should succeed");
}

/*============================================================================
 * File Syscall Tests
 *============================================================================*/

static void test_open_close(void)
{
    TEST_GROUP("open/close tests");

    /* Open a file */
    long fd = linux_sys_open("/test/file", LINUX_O_RDONLY, 0);
    TEST_ASSERT(fd >= 0, "open should succeed");

    if (fd >= 0) {
        long ret = linux_sys_close(fd);
        TEST_ASSERT_EQ(ret, 0, "close should succeed");
    }

    /* openat with AT_FDCWD */
    fd = linux_sys_openat(LINUX_AT_FDCWD, "/test/file2",
                          LINUX_O_RDWR | LINUX_O_CREAT, 0644);
    TEST_ASSERT(fd >= 0, "openat should succeed");

    if (fd >= 0) {
        linux_sys_close(fd);
    }
}

static void test_read_write(void)
{
    TEST_GROUP("read/write tests");

    long fd = linux_sys_open("/test/rw_file", LINUX_O_RDWR | LINUX_O_CREAT, 0644);
    TEST_ASSERT(fd >= 0, "open for read/write test");

    if (fd >= 0) {
        /* Write data */
        const char *data = "Hello, Linux ABI!";
        long written = linux_sys_write(fd, data, strlen(data));
        TEST_ASSERT_EQ(written, (long)strlen(data), "write should return bytes written");

        /* Seek to beginning */
        linux_sys_lseek(fd, 0, 0);

        /* Read data back */
        char buf[64];
        memset(buf, 0, sizeof(buf));
        long nr = linux_sys_read(fd, buf, sizeof(buf));
        TEST_ASSERT(nr > 0, "read should return positive");

        linux_sys_close(fd);
    }
}

static void test_pread_pwrite(void)
{
    TEST_GROUP("pread/pwrite tests");

    long fd = linux_sys_open("/test/pfile", LINUX_O_RDWR | LINUX_O_CREAT, 0644);
    TEST_ASSERT(fd >= 0, "open for pread/pwrite test");

    if (fd >= 0) {
        const char *data = "Position test";
        long written = linux_sys_pwrite64(fd, data, strlen(data), 100);
        TEST_ASSERT_EQ(written, (long)strlen(data), "pwrite should succeed");

        char buf[32];
        long nr = linux_sys_pread64(fd, buf, sizeof(buf), 100);
        TEST_ASSERT(nr > 0, "pread should succeed");

        linux_sys_close(fd);
    }
}

static void test_lseek(void)
{
    TEST_GROUP("lseek tests");

    long fd = linux_sys_open("/test/seek_file", LINUX_O_RDWR | LINUX_O_CREAT, 0644);
    TEST_ASSERT(fd >= 0, "open for lseek test");

    if (fd >= 0) {
        /* Seek to specific position */
        long pos = linux_sys_lseek(fd, 100, 0);  /* SEEK_SET */
        TEST_ASSERT_EQ(pos, 100, "lseek SEEK_SET should return new position");

        /* Seek from current */
        pos = linux_sys_lseek(fd, 50, 1);  /* SEEK_CUR */
        TEST_ASSERT_EQ(pos, 150, "lseek SEEK_CUR should return new position");

        linux_sys_close(fd);
    }
}

static void test_dup(void)
{
    TEST_GROUP("dup tests");

    long fd = linux_sys_open("/test/dup_file", LINUX_O_RDWR | LINUX_O_CREAT, 0644);
    TEST_ASSERT(fd >= 0, "open for dup test");

    if (fd >= 0) {
        /* dup */
        long fd2 = linux_sys_dup(fd);
        TEST_ASSERT(fd2 >= 0, "dup should succeed");
        TEST_ASSERT_NE(fd2, fd, "dup should return different fd");

        /* dup2 */
        long fd3 = linux_sys_dup2(fd, 100);
        TEST_ASSERT_EQ(fd3, 100, "dup2 should return specified fd");

        /* dup3 with flags */
        long fd4 = linux_sys_dup3(fd, 101, LINUX_O_CLOEXEC);
        TEST_ASSERT_EQ(fd4, 101, "dup3 should return specified fd");

        linux_sys_close(fd);
        if (fd2 >= 0) linux_sys_close(fd2);
        if (fd3 >= 0) linux_sys_close(fd3);
        if (fd4 >= 0) linux_sys_close(fd4);
    }
}

static void test_fcntl(void)
{
    TEST_GROUP("fcntl tests");

    long fd = linux_sys_open("/test/fcntl_file", LINUX_O_RDWR | LINUX_O_CREAT, 0644);
    TEST_ASSERT(fd >= 0, "open for fcntl test");

    if (fd >= 0) {
        /* Get flags */
        long flags = linux_sys_fcntl(fd, LINUX_F_GETFL, 0);
        TEST_ASSERT(flags >= 0, "F_GETFL should succeed");

        /* Set flags */
        long ret = linux_sys_fcntl(fd, LINUX_F_SETFL, flags | LINUX_O_NONBLOCK);
        TEST_ASSERT_EQ(ret, 0, "F_SETFL should succeed");

        /* Get FD flags */
        long fd_flags = linux_sys_fcntl(fd, LINUX_F_GETFD, 0);
        TEST_ASSERT(fd_flags >= 0, "F_GETFD should succeed");

        /* Set close-on-exec */
        ret = linux_sys_fcntl(fd, LINUX_F_SETFD, LINUX_FD_CLOEXEC);
        TEST_ASSERT_EQ(ret, 0, "F_SETFD should succeed");

        /* F_DUPFD */
        long newfd = linux_sys_fcntl(fd, LINUX_F_DUPFD, 50);
        TEST_ASSERT_GE(newfd, 50, "F_DUPFD should return fd >= min");

        linux_sys_close(fd);
        if (newfd >= 0) linux_sys_close(newfd);
    }
}

static void test_stat(void)
{
    TEST_GROUP("stat tests");

    /* stat */
    struct linux_stat st;
    long ret = linux_sys_stat("/test/stat_file", &st);
    TEST_ASSERT_EQ(ret, 0, "stat should succeed");
    TEST_ASSERT(st.st_size > 0, "stat should return size");

    /* fstat */
    long fd = linux_sys_open("/test/stat_file", LINUX_O_RDONLY, 0);
    if (fd >= 0) {
        ret = linux_sys_fstat(fd, &st);
        TEST_ASSERT_EQ(ret, 0, "fstat should succeed");
        linux_sys_close(fd);
    }
}

static void test_pipe(void)
{
    TEST_GROUP("pipe tests");

    int pipefd[2];
    long ret = linux_sys_pipe2(pipefd, 0);
    TEST_ASSERT_EQ(ret, 0, "pipe2 should succeed");
    TEST_ASSERT(pipefd[0] >= 0, "pipe read fd should be valid");
    TEST_ASSERT(pipefd[1] >= 0, "pipe write fd should be valid");
    TEST_ASSERT_NE(pipefd[0], pipefd[1], "pipe fds should be different");

    if (ret == 0) {
        linux_sys_close(pipefd[0]);
        linux_sys_close(pipefd[1]);
    }

    /* pipe2 with O_CLOEXEC */
    ret = linux_sys_pipe2(pipefd, LINUX_O_CLOEXEC);
    TEST_ASSERT_EQ(ret, 0, "pipe2 with O_CLOEXEC should succeed");

    if (ret == 0) {
        linux_sys_close(pipefd[0]);
        linux_sys_close(pipefd[1]);
    }
}

/*============================================================================
 * Process Syscall Tests
 *============================================================================*/

static void test_getpid(void)
{
    TEST_GROUP("getpid tests");

    long pid = linux_sys_getpid();
    TEST_ASSERT(pid > 0, "getpid should return positive");

    long tid = linux_sys_gettid();
    TEST_ASSERT(tid > 0, "gettid should return positive");

    /* In main thread, pid == tid */
    TEST_ASSERT_EQ(pid, tid, "main thread pid should equal tid");

    long ppid = linux_sys_getppid();
    TEST_ASSERT(ppid >= 0, "getppid should return non-negative");
}

static void test_tid_address(void)
{
    TEST_GROUP("set_tid_address tests");

    int tid_storage;
    long ret = linux_sys_set_tid_address(&tid_storage);
    TEST_ASSERT(ret > 0, "set_tid_address should return tid");
}

/*============================================================================
 * Signal Syscall Tests
 *============================================================================*/

static volatile int signal_received = 0;

static void test_signal_handler(int signo)
{
    (void)signo;
    signal_received = 1;
}

static void test_sigaction(void)
{
    TEST_GROUP("sigaction tests");

    struct linux_sigaction act, oldact;

    /* Install handler */
    memset(&act, 0, sizeof(act));
    act.sa_handler = test_signal_handler;
    act.sa_flags = 0;
    act.sa_mask = 0;

    long ret = linux_sys_rt_sigaction(LINUX_SIGUSR1, &act, NULL, 8);
    TEST_ASSERT_EQ(ret, 0, "rt_sigaction install should succeed");

    /* Get current handler */
    ret = linux_sys_rt_sigaction(LINUX_SIGUSR1, NULL, &oldact, 8);
    TEST_ASSERT_EQ(ret, 0, "rt_sigaction query should succeed");
    TEST_ASSERT_EQ((void *)oldact.sa_handler, (void *)test_signal_handler,
                   "handler should be installed");

    /* Cannot change SIGKILL */
    ret = linux_sys_rt_sigaction(LINUX_SIGKILL, &act, NULL, 8);
    TEST_ASSERT_EQ(ret, -LINUX_EINVAL, "cannot change SIGKILL handler");

    /* Cannot change SIGSTOP */
    ret = linux_sys_rt_sigaction(LINUX_SIGSTOP, &act, NULL, 8);
    TEST_ASSERT_EQ(ret, -LINUX_EINVAL, "cannot change SIGSTOP handler");
}

static void test_sigprocmask(void)
{
    TEST_GROUP("sigprocmask tests");

    uint64_t set, oldset;

    /* Get current mask */
    long ret = linux_sys_rt_sigprocmask(LINUX_SIG_SETMASK, NULL, &oldset, 8);
    TEST_ASSERT_EQ(ret, 0, "rt_sigprocmask query should succeed");

    /* Block SIGUSR1 */
    set = (1UL << (LINUX_SIGUSR1 - 1));
    ret = linux_sys_rt_sigprocmask(LINUX_SIG_BLOCK, &set, NULL, 8);
    TEST_ASSERT_EQ(ret, 0, "rt_sigprocmask SIG_BLOCK should succeed");

    /* Unblock SIGUSR1 */
    ret = linux_sys_rt_sigprocmask(LINUX_SIG_UNBLOCK, &set, NULL, 8);
    TEST_ASSERT_EQ(ret, 0, "rt_sigprocmask SIG_UNBLOCK should succeed");

    /* Invalid how */
    ret = linux_sys_rt_sigprocmask(99, &set, NULL, 8);
    TEST_ASSERT_EQ(ret, -LINUX_EINVAL, "invalid how should fail");

    /* Wrong sigsetsize */
    ret = linux_sys_rt_sigprocmask(LINUX_SIG_BLOCK, &set, NULL, 4);
    TEST_ASSERT_EQ(ret, -LINUX_EINVAL, "wrong sigsetsize should fail");
}

static void test_kill(void)
{
    TEST_GROUP("kill tests");

    /* Send signal 0 to check process exists */
    long ret = linux_sys_kill(1, 0);
    TEST_ASSERT_EQ(ret, 0, "kill signal 0 should succeed");

    /* Invalid signal */
    ret = linux_sys_kill(1, 100);
    TEST_ASSERT_EQ(ret, -LINUX_EINVAL, "invalid signal should fail");
}

static void test_alarm(void)
{
    TEST_GROUP("alarm tests");

    /* Set alarm */
    unsigned int remaining = linux_sys_alarm(10);
    TEST_ASSERT_EQ(remaining, 0, "first alarm should return 0");

    /* Set another alarm */
    remaining = linux_sys_alarm(5);
    TEST_ASSERT_EQ(remaining, 10, "second alarm should return previous");

    /* Cancel alarm */
    remaining = linux_sys_alarm(0);
    TEST_ASSERT_EQ(remaining, 5, "alarm(0) should return remaining");
}

/*============================================================================
 * Epoll Syscall Tests
 *============================================================================*/

static void test_epoll_create(void)
{
    TEST_GROUP("epoll_create tests");

    /* epoll_create (size ignored) */
    long epfd = linux_sys_epoll_create(10);
    TEST_ASSERT(epfd >= 0, "epoll_create should succeed");

    if (epfd >= 0) {
        linux_sys_close(epfd);
    }

    /* epoll_create1 */
    epfd = linux_sys_epoll_create1(0);
    TEST_ASSERT(epfd >= 0, "epoll_create1 should succeed");

    if (epfd >= 0) {
        linux_sys_close(epfd);
    }

    /* epoll_create1 with CLOEXEC */
    epfd = linux_sys_epoll_create1(EPOLL_CLOEXEC);
    TEST_ASSERT(epfd >= 0, "epoll_create1 with CLOEXEC should succeed");

    if (epfd >= 0) {
        linux_sys_close(epfd);
    }
}

static void test_epoll_ctl(void)
{
    TEST_GROUP("epoll_ctl tests");

    long epfd = linux_sys_epoll_create1(0);
    TEST_ASSERT(epfd >= 0, "epoll_create for ctl test");

    if (epfd >= 0) {
        int pipefd[2];
        linux_sys_pipe2(pipefd, 0);

        struct linux_epoll_event ev;
        ev.events = EPOLLIN;
        ev.data = pipefd[0];

        /* Add fd */
        long ret = linux_sys_epoll_ctl(epfd, EPOLL_CTL_ADD, pipefd[0], &ev);
        TEST_ASSERT_EQ(ret, 0, "EPOLL_CTL_ADD should succeed");

        /* Modify fd */
        ev.events = EPOLLIN | EPOLLOUT;
        ret = linux_sys_epoll_ctl(epfd, EPOLL_CTL_MOD, pipefd[0], &ev);
        TEST_ASSERT_EQ(ret, 0, "EPOLL_CTL_MOD should succeed");

        /* Delete fd */
        ret = linux_sys_epoll_ctl(epfd, EPOLL_CTL_DEL, pipefd[0], NULL);
        TEST_ASSERT_EQ(ret, 0, "EPOLL_CTL_DEL should succeed");

        /* Add again */
        ev.events = EPOLLIN;
        ret = linux_sys_epoll_ctl(epfd, EPOLL_CTL_ADD, pipefd[0], &ev);
        TEST_ASSERT_EQ(ret, 0, "re-add should succeed");

        linux_sys_close(pipefd[0]);
        linux_sys_close(pipefd[1]);
        linux_sys_close(epfd);
    }
}

static void test_epoll_wait(void)
{
    TEST_GROUP("epoll_wait tests");

    long epfd = linux_sys_epoll_create1(0);
    TEST_ASSERT(epfd >= 0, "epoll_create for wait test");

    if (epfd >= 0) {
        struct linux_epoll_event events[10];

        /* Wait with timeout 0 (poll) */
        long ret = linux_sys_epoll_wait(epfd, events, 10, 0);
        TEST_ASSERT_EQ(ret, 0, "epoll_wait on empty set should return 0");

        /* Invalid maxevents */
        ret = linux_sys_epoll_wait(epfd, events, 0, 0);
        TEST_ASSERT_EQ(ret, -LINUX_EINVAL, "maxevents=0 should fail");

        ret = linux_sys_epoll_wait(epfd, events, -1, 0);
        TEST_ASSERT_EQ(ret, -LINUX_EINVAL, "negative maxevents should fail");

        linux_sys_close(epfd);
    }
}

/*============================================================================
 * Futex Syscall Tests
 *============================================================================*/

static void test_futex(void)
{
    TEST_GROUP("futex tests");

    uint32_t futex_val = 1;

    /* FUTEX_WAKE with no waiters */
    long ret = linux_sys_futex(&futex_val, FUTEX_WAKE, 1, NULL, NULL, 0);
    TEST_ASSERT_EQ(ret, 0, "FUTEX_WAKE with no waiters should return 0");

    /* FUTEX_WAIT with non-matching value (should return immediately) */
    struct linux_timespec ts = { .tv_sec = 0, .tv_nsec = 1000000 }; /* 1ms */
    ret = linux_sys_futex(&futex_val, FUTEX_WAIT, 999, &ts, NULL, 0);
    TEST_ASSERT_EQ(ret, -LINUX_EAGAIN, "FUTEX_WAIT with wrong val should return EAGAIN");

    /* FUTEX_WAKE_PRIVATE */
    ret = linux_sys_futex(&futex_val, FUTEX_WAKE_PRIVATE, 1, NULL, NULL, 0);
    TEST_ASSERT_EQ(ret, 0, "FUTEX_WAKE_PRIVATE should succeed");
}

/*============================================================================
 * Constant Validation Tests
 *============================================================================*/

static void test_constants(void)
{
    TEST_GROUP("constant validation");

    /* Syscall numbers should match Linux */
    TEST_ASSERT_EQ(__NR_read, 0, "__NR_read == 0");
    TEST_ASSERT_EQ(__NR_write, 1, "__NR_write == 1");
    TEST_ASSERT_EQ(__NR_open, 2, "__NR_open == 2");
    TEST_ASSERT_EQ(__NR_close, 3, "__NR_close == 3");
    TEST_ASSERT_EQ(__NR_mmap, 9, "__NR_mmap == 9");
    TEST_ASSERT_EQ(__NR_clone, 56, "__NR_clone == 56");
    TEST_ASSERT_EQ(__NR_fork, 57, "__NR_fork == 57");
    TEST_ASSERT_EQ(__NR_execve, 59, "__NR_execve == 59");
    TEST_ASSERT_EQ(__NR_exit, 60, "__NR_exit == 60");
    TEST_ASSERT_EQ(__NR_futex, 202, "__NR_futex == 202");
    TEST_ASSERT_EQ(__NR_epoll_create, 213, "__NR_epoll_create == 213");

    /* Signal numbers */
    TEST_ASSERT_EQ(LINUX_SIGHUP, 1, "SIGHUP == 1");
    TEST_ASSERT_EQ(LINUX_SIGINT, 2, "SIGINT == 2");
    TEST_ASSERT_EQ(LINUX_SIGKILL, 9, "SIGKILL == 9");
    TEST_ASSERT_EQ(LINUX_SIGSTOP, 19, "SIGSTOP == 19");

    /* Error numbers */
    TEST_ASSERT_EQ(LINUX_EPERM, 1, "EPERM == 1");
    TEST_ASSERT_EQ(LINUX_ENOENT, 2, "ENOENT == 2");
    TEST_ASSERT_EQ(LINUX_EINVAL, 22, "EINVAL == 22");
    TEST_ASSERT_EQ(LINUX_ENOSYS, 38, "ENOSYS == 38");

    /* Clone flags */
    TEST_ASSERT_EQ(CLONE_VM, 0x100, "CLONE_VM == 0x100");
    TEST_ASSERT_EQ(CLONE_THREAD, 0x10000, "CLONE_THREAD == 0x10000");
}

/*============================================================================
 * Structure Size Tests
 *============================================================================*/

static void test_struct_sizes(void)
{
    TEST_GROUP("structure size validation");

    /* Verify structure sizes match Linux x86_64 ABI */
    TEST_ASSERT_EQ(sizeof(struct linux_stat), 144, "linux_stat size");
    TEST_ASSERT_EQ(sizeof(struct linux_timespec), 16, "linux_timespec size");
    TEST_ASSERT_EQ(sizeof(struct linux_timeval), 16, "linux_timeval size");
    TEST_ASSERT_EQ(sizeof(struct linux_iovec), 16, "linux_iovec size");
    TEST_ASSERT_EQ(sizeof(struct linux_epoll_event), 12, "linux_epoll_event size");
    TEST_ASSERT_EQ(sizeof(struct linux_clone_args), 88, "linux_clone_args size");
}

/*============================================================================
 * Main Test Runner
 *============================================================================*/

int main(int argc, char *argv[])
{
    (void)argc;
    (void)argv;

    printf("==============================================\n");
    printf("Linux ABI Comprehensive Test Suite\n");
    printf("==============================================\n");

    /* Memory syscall tests */
    test_mmap_basic();
    test_mmap_fixed();
    test_mprotect();
    test_brk();
    test_mremap();
    test_madvise();
    test_mlock();

    /* File syscall tests */
    test_open_close();
    test_read_write();
    test_pread_pwrite();
    test_lseek();
    test_dup();
    test_fcntl();
    test_stat();
    test_pipe();

    /* Process syscall tests */
    test_getpid();
    test_tid_address();

    /* Signal syscall tests */
    test_sigaction();
    test_sigprocmask();
    test_kill();
    test_alarm();

    /* Epoll syscall tests */
    test_epoll_create();
    test_epoll_ctl();
    test_epoll_wait();

    /* Futex syscall tests */
    test_futex();

    /* Constant validation */
    test_constants();
    test_struct_sizes();

    /* Summary */
    printf("\n==============================================\n");
    printf("Test Results: %d/%d passed (%d failed)\n",
           tests_passed, tests_run, tests_failed);
    printf("==============================================\n");

    return tests_failed > 0 ? 1 : 0;
}

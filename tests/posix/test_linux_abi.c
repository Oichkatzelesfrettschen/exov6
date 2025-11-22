#include <stdio.h>
#include <assert.h>
#include <errno.h>
#include "../../include/linux_compat.h"

/* Mocks for libos functions */
int mock_getpid_ret = 1234;
int libos_getpid(void) {
    return mock_getpid_ret;
}

int mock_read_fd;
void *mock_read_buf;
size_t mock_read_count;
int libos_read(int fd, void *buf, size_t count) {
    mock_read_fd = fd;
    mock_read_buf = buf;
    mock_read_count = count;
    return (int)count;
}

/* Stubs for others to satisfy linker if we were linking,
   but since we include the C file, we need to define all used functions
   or ensure the compiler doesn't complain about missing symbols if we don't call them.
   However, we are including the C file, so the compiler sees the calls.
   We need stubs for EVERYTHING called in linux_abi.c
*/

int libos_open(const char *path, int flags, int mode) { return -1; }
int libos_close(int fd) { return 0; }
int libos_write(int fd, const void *buf, size_t count) { return count; }
long libos_lseek(int fd, long offset, int whence) { return 0; }
int libos_stat(const char *path, void *st) { return 0; }
int libos_mkdir(const char *path) { return 0; }
int libos_rmdir(const char *path) { return 0; }
int libos_unlink(const char *path) { return 0; }
int libos_rename(const char *oldpath, const char *newpath) { return 0; }
int libos_fork(void) { return 0; }
int libos_execve(const char *path, char *const argv[], char *const envp[]) { return -1; }
void libos_exit(int status) { }
int libos_waitpid(int pid, int *status, int flags) { return -1; }
void *libos_mmap(void *addr, size_t length, int prot, int flags, int fd, long offset) { return (void*)-1; }
int libos_munmap(void *addr, size_t length) { return 0; }
int libos_socket(int domain, int type, int protocol) { return -1; }
int libos_bind(int fd, const void *addr, int len) { return -1; }
int libos_connect(int fd, const void *addr, int len) { return -1; }
int libos_listen(int fd, int backlog) { return -1; }
int libos_accept(int fd, void *addr, int *len) { return -1; }
int libos_send(int fd, const void *buf, size_t len, int flags) { return -1; }
int libos_recv(int fd, void *buf, size_t len, int flags) { return -1; }
long libos_sendto(int fd, const void *buf, size_t len, int flags, const void *dest_addr, int addrlen) { return len; }
long libos_recvfrom(int fd, void *buf, size_t len, int flags, void *src_addr, int *addrlen) { return 0; }
int libos_sched_setscheduler(void) { return 0; }
int libos_sched_getparam(void) { return 0; }
int libos_sched_getscheduler(void) { return 0; }
int libos_chdir(const char *path) { return 0; }
char *libos_getcwd(char *buf, size_t size) { return buf; }

/* Include the implementation under test */
#include "../../libos/posix/linux_abi.c"

int main() {
    printf("Testing Linux Syscall Dispatcher...\n");

    /* Test 1: invalid syscall */
    long ret = linux_syscall_dispatch(9999, 0, 0, 0, 0, 0, 0);
    assert(ret == -ENOSYS);
    printf("Test 1 Passed: Invalid syscall returns -ENOSYS\n");

    /* Test 2: getpid */
    ret = linux_syscall_dispatch(LINUX_SYS_getpid, 0, 0, 0, 0, 0, 0);
    assert(ret == 1234);
    printf("Test 2 Passed: getpid returns mocked value\n");

    /* Test 3: read (checking argument passing) */
    char buf[10];
    ret = linux_syscall_dispatch(LINUX_SYS_read, 5, (long)buf, 10, 0, 0, 0);
    assert(ret == 10);
    assert(mock_read_fd == 5);
    assert(mock_read_buf == buf);
    assert(mock_read_count == 10);
    printf("Test 3 Passed: read arguments passed correctly\n");

    printf("All Linux ABI tests passed.\n");
    return 0;
}

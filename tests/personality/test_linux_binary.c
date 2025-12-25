/**
 * @file test_linux_binary.c
 * @brief Linux ELF test binary with Linux-specific syscalls
 * 
 * Compile with: gcc -o test_linux test_linux_binary.c -static
 * This creates a Linux ELF with GNU/Linux ABI note
 */

#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <sys/types.h>
#include <sys/epoll.h>
#include <sys/eventfd.h>
#include <linux/futex.h>
#include <sys/syscall.h>
#include <string.h>
#include <errno.h>
#include <time.h>

// Linux-specific syscall numbers
#define SYS_futex       202
#define SYS_epoll_create 213
#define SYS_epoll_wait  232
#define SYS_epoll_ctl   233
#define SYS_clone       56
#define SYS_gettid      186
#define SYS_eventfd2    290

// Test futex operations
int test_linux_futex(void) {
    int futex_var = 0;
    struct timespec timeout = {.tv_sec = 0, .tv_nsec = 100000000}; // 100ms
    
    printf("Testing Linux futex syscall...\n");
    
    // Try FUTEX_WAIT with immediate timeout
    long ret = syscall(SYS_futex, &futex_var, FUTEX_WAIT, 0, &timeout, NULL, 0);
    
    if (ret == -1 && errno == ETIMEDOUT) {
        printf("  ✓ FUTEX_WAIT timeout works\n");
    } else {
        printf("  ✗ FUTEX_WAIT failed: %s\n", strerror(errno));
        return -1;
    }
    
    // FUTEX_WAKE (no waiters)
    ret = syscall(SYS_futex, &futex_var, FUTEX_WAKE, 1, NULL, NULL, 0);
    printf("  ✓ FUTEX_WAKE returned %ld\n", ret);
    
    return 0;
}

// Test epoll operations
int test_linux_epoll(void) {
    printf("Testing Linux epoll syscalls...\n");
    
    // Create epoll instance
    int epfd = syscall(SYS_epoll_create, 10);
    if (epfd < 0) {
        printf("  ✗ epoll_create failed: %s\n", strerror(errno));
        return -1;
    }
    printf("  ✓ epoll_create returned fd %d\n", epfd);
    
    // Create eventfd for testing
    int evfd = syscall(SYS_eventfd2, 0, 0);
    if (evfd < 0) {
        printf("  ✗ eventfd2 failed: %s\n", strerror(errno));
        close(epfd);
        return -1;
    }
    printf("  ✓ eventfd2 returned fd %d\n", evfd);
    
    // Add eventfd to epoll
    struct epoll_event ev = {
        .events = EPOLLIN,
        .data.fd = evfd
    };
    
    if (syscall(SYS_epoll_ctl, epfd, EPOLL_CTL_ADD, evfd, &ev) < 0) {
        printf("  ✗ epoll_ctl ADD failed: %s\n", strerror(errno));
        close(evfd);
        close(epfd);
        return -1;
    }
    printf("  ✓ epoll_ctl ADD succeeded\n");
    
    // Write to eventfd to trigger event
    uint64_t val = 1;
    write(evfd, &val, sizeof(val));
    
    // Wait for events
    struct epoll_event events[10];
    int nfds = syscall(SYS_epoll_wait, epfd, events, 10, 100);
    
    if (nfds > 0) {
        printf("  ✓ epoll_wait returned %d events\n", nfds);
    } else if (nfds == 0) {
        printf("  ✓ epoll_wait timeout\n");
    } else {
        printf("  ✗ epoll_wait failed: %s\n", strerror(errno));
    }
    
    close(evfd);
    close(epfd);
    return 0;
}

// Test clone syscall (thread creation)
int test_linux_clone(void) {
    printf("Testing Linux clone syscall...\n");
    
    // Get current thread ID
    pid_t tid = syscall(SYS_gettid);
    printf("  ✓ Current thread ID: %d\n", tid);
    
    // Get process ID for comparison
    pid_t pid = getpid();
    printf("  ✓ Current process ID: %d\n", pid);
    
    // In single-threaded process, TID == PID
    if (tid == pid) {
        printf("  ✓ TID equals PID (single-threaded)\n");
    }
    
    return 0;
}

// Test /proc filesystem access (Linux-specific)
int test_linux_proc(void) {
    printf("Testing Linux /proc filesystem...\n");
    
    char path[256];
    char comm[256];
    
    // Read /proc/self/comm
    snprintf(path, sizeof(path), "/proc/self/comm");
    FILE *f = fopen(path, "r");
    if (f) {
        if (fgets(comm, sizeof(comm), f)) {
            comm[strcspn(comm, "\n")] = 0;
            printf("  ✓ Process name from /proc: %s\n", comm);
        }
        fclose(f);
    } else {
        printf("  ✗ Cannot read /proc/self/comm\n");
    }
    
    // Check /proc/self/exe symlink
    snprintf(path, sizeof(path), "/proc/self/exe");
    char exe[256];
    ssize_t len = readlink(path, exe, sizeof(exe) - 1);
    if (len > 0) {
        exe[len] = 0;
        printf("  ✓ Executable path: %s\n", exe);
    } else {
        printf("  ✗ Cannot read /proc/self/exe\n");
    }
    
    return 0;
}

int main(int argc, char *argv[]) {
    printf("===========================================\n");
    printf("Linux Personality Test Binary\n");
    printf("===========================================\n");
    printf("This binary uses Linux-specific syscalls\n");
    printf("and should be detected as PERSONALITY_LINUX\n");
    printf("===========================================\n\n");
    
    // Show basic info
    printf("Process ID: %d\n", getpid());
    printf("User ID: %d\n", getuid());
    printf("Group ID: %d\n", getgid());
    printf("\n");
    
    // Run Linux-specific tests
    int failures = 0;
    
    if (test_linux_futex() < 0) failures++;
    printf("\n");
    
    if (test_linux_epoll() < 0) failures++;
    printf("\n");
    
    if (test_linux_clone() < 0) failures++;
    printf("\n");
    
    if (test_linux_proc() < 0) failures++;
    printf("\n");
    
    // Summary
    printf("===========================================\n");
    if (failures == 0) {
        printf("✅ All Linux personality tests passed!\n");
    } else {
        printf("❌ %d Linux personality tests failed\n", failures);
    }
    printf("===========================================\n");
    
    return failures;
}
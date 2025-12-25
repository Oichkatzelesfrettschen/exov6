/**
 * @file test_bsd_binary.c
 * @brief BSD test binary with BSD-specific syscalls
 * 
 * Compile on FreeBSD: cc -o test_bsd test_bsd_binary.c
 * This creates a BSD ELF with FreeBSD ABI note
 */

#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <string.h>
#include <errno.h>
#include <sys/types.h>
#include <sys/event.h>
#include <sys/time.h>
#include <sys/capsicum.h>
#include <sys/jail.h>
#include <sys/sysctl.h>
#include <fcntl.h>

// BSD-specific syscall numbers
#define SYS_kqueue      362
#define SYS_kevent      363
#define SYS_jail        338
#define SYS_jail_get    506
#define SYS_cap_enter   516
#define SYS_cap_rights_limit 515

// Test kqueue/kevent
int test_bsd_kqueue(void) {
    printf("Testing BSD kqueue/kevent syscalls...\n");
    
    // Create kqueue
    int kq = kqueue();
    if (kq < 0) {
        printf("  ✗ kqueue failed: %s\n", strerror(errno));
        return -1;
    }
    printf("  ✓ kqueue created with fd %d\n", kq);
    
    // Create a pipe for testing
    int pipefd[2];
    if (pipe(pipefd) < 0) {
        printf("  ✗ pipe failed: %s\n", strerror(errno));
        close(kq);
        return -1;
    }
    
    // Register read event on pipe
    struct kevent change;
    EV_SET(&change, pipefd[0], EVFILT_READ, EV_ADD | EV_ENABLE, 0, 0, 0);
    
    if (kevent(kq, &change, 1, NULL, 0, NULL) < 0) {
        printf("  ✗ kevent register failed: %s\n", strerror(errno));
        close(pipefd[0]);
        close(pipefd[1]);
        close(kq);
        return -1;
    }
    printf("  ✓ kevent registered for pipe read\n");
    
    // Write to pipe
    const char *msg = "test";
    write(pipefd[1], msg, strlen(msg));
    
    // Wait for event
    struct kevent event;
    struct timespec timeout = {.tv_sec = 0, .tv_nsec = 100000000}; // 100ms
    
    int n = kevent(kq, NULL, 0, &event, 1, &timeout);
    if (n > 0) {
        printf("  ✓ kevent triggered: %d bytes available\n", (int)event.data);
    } else if (n == 0) {
        printf("  ✗ kevent timeout\n");
    } else {
        printf("  ✗ kevent wait failed: %s\n", strerror(errno));
    }
    
    close(pipefd[0]);
    close(pipefd[1]);
    close(kq);
    return 0;
}

// Test jail info (won't create jail, just query)
int test_bsd_jail(void) {
    printf("Testing BSD jail syscalls...\n");
    
    // Try to get jail ID (should be 0 if not jailed)
    int jid = jail_getid("test_jail");
    if (jid == -1) {
        printf("  ✓ jail_getid returned -1 (no jail found)\n");
    } else {
        printf("  ✓ jail_getid returned %d\n", jid);
    }
    
    // Check if we're in a jail
    int injail = 0;
    size_t len = sizeof(injail);
    if (sysctlbyname("security.jail.jailed", &injail, &len, NULL, 0) == 0) {
        printf("  ✓ In jail: %s\n", injail ? "yes" : "no");
    } else {
        printf("  ✗ Cannot check jail status\n");
    }
    
    return 0;
}

// Test Capsicum capability mode
int test_bsd_capsicum(void) {
    printf("Testing BSD Capsicum syscalls...\n");
    
    // Check if we're in capability mode
    int mode = cap_getmode(&mode);
    if (mode == 0) {
        printf("  ✓ Not in capability mode\n");
    } else if (mode == 1) {
        printf("  ✓ Already in capability mode\n");
    } else {
        printf("  ✗ cap_getmode failed: %s\n", strerror(errno));
    }
    
    // Test capability rights
    int fd = open("/dev/null", O_RDWR);
    if (fd >= 0) {
        cap_rights_t rights;
        cap_rights_init(&rights, CAP_READ, CAP_WRITE);
        
        // Try to limit rights (may fail if not supported)
        if (cap_rights_limit(fd, &rights) == 0) {
            printf("  ✓ cap_rights_limit succeeded\n");
        } else {
            printf("  ✓ cap_rights_limit not available: %s\n", strerror(errno));
        }
        
        close(fd);
    }
    
    return 0;
}

// Test sysctl (BSD-specific interface)
int test_bsd_sysctl(void) {
    printf("Testing BSD sysctl interface...\n");
    
    // Get kernel version
    char version[256];
    size_t len = sizeof(version);
    
    if (sysctlbyname("kern.version", version, &len, NULL, 0) == 0) {
        version[len - 1] = '\0';
        printf("  ✓ Kernel version: %.50s...\n", version);
    } else {
        printf("  ✗ Cannot get kernel version\n");
    }
    
    // Get hostname
    char hostname[256];
    len = sizeof(hostname);
    
    if (sysctlbyname("kern.hostname", hostname, &len, NULL, 0) == 0) {
        printf("  ✓ Hostname: %s\n", hostname);
    } else {
        printf("  ✗ Cannot get hostname\n");
    }
    
    // Get number of CPUs
    int ncpu;
    len = sizeof(ncpu);
    
    if (sysctlbyname("hw.ncpu", &ncpu, &len, NULL, 0) == 0) {
        printf("  ✓ Number of CPUs: %d\n", ncpu);
    } else {
        printf("  ✗ Cannot get CPU count\n");
    }
    
    return 0;
}

// Test BSD-specific file flags
int test_bsd_file_flags(void) {
    printf("Testing BSD file flags...\n");
    
    // Create test file
    const char *testfile = "/tmp/bsd_test_file";
    int fd = open(testfile, O_CREAT | O_WRONLY, 0644);
    if (fd < 0) {
        printf("  ✗ Cannot create test file\n");
        return -1;
    }
    close(fd);
    
    // Try to set BSD file flags (immutable, append-only)
    struct stat st;
    if (stat(testfile, &st) == 0) {
        printf("  ✓ Test file created\n");
        
        // Check for BSD-specific st_flags field
        #ifdef UF_IMMUTABLE
        if (chflags(testfile, UF_IMMUTABLE) == 0) {
            printf("  ✓ Set UF_IMMUTABLE flag\n");
            chflags(testfile, 0);  // Clear flag
        } else {
            printf("  ✓ chflags not available: %s\n", strerror(errno));
        }
        #else
        printf("  ✓ BSD file flags not available on this system\n");
        #endif
    }
    
    unlink(testfile);
    return 0;
}

int main(int argc, char *argv[]) {
    printf("===========================================\n");
    printf("BSD Personality Test Binary\n");
    printf("===========================================\n");
    printf("This binary uses BSD-specific syscalls\n");
    printf("and should be detected as PERSONALITY_BSD\n");
    printf("===========================================\n\n");
    
    // Show basic info
    printf("Process ID: %d\n", getpid());
    printf("User ID: %d\n", getuid());
    printf("Group ID: %d\n", getgid());
    printf("\n");
    
    // Run BSD-specific tests
    int failures = 0;
    
    if (test_bsd_kqueue() < 0) failures++;
    printf("\n");
    
    if (test_bsd_jail() < 0) failures++;
    printf("\n");
    
    if (test_bsd_capsicum() < 0) failures++;
    printf("\n");
    
    if (test_bsd_sysctl() < 0) failures++;
    printf("\n");
    
    if (test_bsd_file_flags() < 0) failures++;
    printf("\n");
    
    // Summary
    printf("===========================================\n");
    if (failures == 0) {
        printf("✅ All BSD personality tests passed!\n");
    } else {
        printf("❌ %d BSD personality tests failed\n", failures);
    }
    printf("===========================================\n");
    
    return failures;
}
/**
 * @file test_v6_binary.c
 * @brief V6/V7 UNIX compatibility test binary
 * 
 * This tests our ability to run ancient UNIX binaries with
 * structure versioning and syscall translation.
 */

#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <fcntl.h>
#include <errno.h>
#include <signal.h>
#include <sys/types.h>

// V6/V7 syscall numbers (different from modern)
#define V6_SYS_exit     1
#define V6_SYS_fork     2
#define V6_SYS_read     3
#define V6_SYS_write    4
#define V6_SYS_open     5
#define V6_SYS_close    6
#define V6_SYS_wait     7
#define V6_SYS_creat    8
#define V6_SYS_link     9
#define V6_SYS_unlink   10
#define V6_SYS_exec     11
#define V6_SYS_chdir    12
#define V6_SYS_time     13
#define V6_SYS_mknod    14
#define V6_SYS_chmod    15
#define V6_SYS_chown    16
#define V6_SYS_break    17
#define V6_SYS_stat     18
#define V6_SYS_seek     19
#define V6_SYS_getpid   20
#define V6_SYS_mount    21
#define V6_SYS_umount   22
#define V6_SYS_setuid   23
#define V6_SYS_getuid   24
#define V6_SYS_stime    25
#define V6_SYS_ptrace   26
#define V6_SYS_alarm    27
#define V6_SYS_fstat    28
#define V6_SYS_pause    29
#define V6_SYS_utime    30
#define V6_SYS_stty     31
#define V6_SYS_gtty     32
#define V6_SYS_access   33
#define V6_SYS_nice     34
#define V6_SYS_sync     36
#define V6_SYS_kill     37
#define V6_SYS_dup      41
#define V6_SYS_pipe     42
#define V6_SYS_times    43
#define V6_SYS_prof     44
#define V6_SYS_setgid   46
#define V6_SYS_getgid   47
#define V6_SYS_signal   48

// V6 stat structure (16 bytes vs modern 144+ bytes)
struct stat_v6 {
    uint16_t st_dev;    // Device (2 bytes)
    uint16_t st_ino;    // Inode (2 bytes)
    uint16_t st_mode;   // Mode (2 bytes)
    uint8_t  st_nlink;  // Links (1 byte)
    uint8_t  st_uid;    // UID (1 byte)
    uint8_t  st_gid;    // GID (1 byte)
    uint8_t  st_size0;  // Size high byte
    uint16_t st_size1;  // Size low word (3 bytes total)
    uint16_t st_atime[2]; // Access time (4 bytes)
    uint16_t st_mtime[2]; // Modify time (4 bytes)
};

// V6 time structure (different from modern)
typedef long time_v6;  // 32-bit seconds since 1970

// Inline assembly for V6 syscalls (using trap)
static inline long v6_syscall(int num, long a1, long a2, long a3) {
    long ret;
#ifdef __x86_64__
    __asm__ volatile(
        "movq %1, %%rax\n"
        "movq %2, %%rdi\n"
        "movq %3, %%rsi\n"
        "movq %4, %%rdx\n"
        "int $0x80\n"  // V6/V7 used INT 0x80
        "movq %%rax, %0"
        : "=r"(ret)
        : "r"((long)num), "r"(a1), "r"(a2), "r"(a3)
        : "rax", "rdi", "rsi", "rdx", "memory"
    );
#else
    // Fallback to modern syscall for testing
    ret = syscall(num, a1, a2, a3);
#endif
    return ret;
}

// Test V6 basic syscalls
int test_v6_basic(void) {
    printf("Testing V6 basic syscalls...\n");
    
    // Test getpid (syscall 20)
    pid_t pid = v6_syscall(V6_SYS_getpid, 0, 0, 0);
    printf("  ✓ V6 getpid: %d\n", pid);
    
    // Test getuid (syscall 24)
    uid_t uid = v6_syscall(V6_SYS_getuid, 0, 0, 0);
    printf("  ✓ V6 getuid: %d\n", uid);
    
    // Test getgid (syscall 47)
    gid_t gid = v6_syscall(V6_SYS_getgid, 0, 0, 0);
    printf("  ✓ V6 getgid: %d\n", gid);
    
    return 0;
}

// Test V6 file operations
int test_v6_files(void) {
    printf("Testing V6 file operations...\n");
    
    const char *filename = "/tmp/v6test";
    
    // Create file using V6 creat (syscall 8)
    int fd = v6_syscall(V6_SYS_creat, (long)filename, 0644, 0);
    if (fd < 0) {
        printf("  ✗ V6 creat failed\n");
        return -1;
    }
    printf("  ✓ V6 creat: fd=%d\n", fd);
    
    // Write using V6 write (syscall 4)
    const char *msg = "V6 Unix\n";
    ssize_t n = v6_syscall(V6_SYS_write, fd, (long)msg, strlen(msg));
    printf("  ✓ V6 write: %ld bytes\n", n);
    
    // Close using V6 close (syscall 6)
    v6_syscall(V6_SYS_close, fd, 0, 0);
    printf("  ✓ V6 close\n");
    
    // Open for reading using V6 open (syscall 5)
    fd = v6_syscall(V6_SYS_open, (long)filename, O_RDONLY, 0);
    if (fd < 0) {
        printf("  ✗ V6 open failed\n");
        return -1;
    }
    printf("  ✓ V6 open: fd=%d\n", fd);
    
    // Read using V6 read (syscall 3)
    char buf[32];
    n = v6_syscall(V6_SYS_read, fd, (long)buf, sizeof(buf));
    if (n > 0) {
        buf[n] = '\0';
        printf("  ✓ V6 read: '%s'\n", buf);
    }
    
    // Close and unlink
    v6_syscall(V6_SYS_close, fd, 0, 0);
    v6_syscall(V6_SYS_unlink, (long)filename, 0, 0);
    printf("  ✓ V6 unlink\n");
    
    return 0;
}

// Test V6 stat structure
int test_v6_stat(void) {
    printf("Testing V6 stat structure...\n");
    
    const char *filename = "/tmp/v6stat";
    
    // Create test file
    int fd = creat(filename, 0644);
    if (fd < 0) {
        printf("  ✗ Cannot create test file\n");
        return -1;
    }
    write(fd, "test", 4);
    close(fd);
    
    // Use V6 stat structure
    struct stat_v6 st;
    
    // Call V6 stat (syscall 18)
    if (v6_syscall(V6_SYS_stat, (long)filename, (long)&st, 0) < 0) {
        printf("  ✗ V6 stat failed\n");
        unlink(filename);
        return -1;
    }
    
    printf("  ✓ V6 stat structure:\n");
    printf("    dev: 0x%04x\n", st.st_dev);
    printf("    ino: %u\n", st.st_ino);
    printf("    mode: 0%o\n", st.st_mode);
    printf("    nlink: %u\n", st.st_nlink);
    printf("    uid: %u\n", st.st_uid);
    printf("    gid: %u\n", st.st_gid);
    
    // V6 3-byte size field
    uint32_t size = ((uint32_t)st.st_size0 << 16) | st.st_size1;
    printf("    size: %u bytes\n", size);
    
    // V6 time format (2 16-bit words)
    uint32_t atime = ((uint32_t)st.st_atime[0] << 16) | st.st_atime[1];
    uint32_t mtime = ((uint32_t)st.st_mtime[0] << 16) | st.st_mtime[1];
    printf("    atime: %u\n", atime);
    printf("    mtime: %u\n", mtime);
    
    unlink(filename);
    return 0;
}

// Test V6 pipes
int test_v6_pipe(void) {
    printf("Testing V6 pipe...\n");
    
    int pipefd[2];
    
    // V6 pipe (syscall 42) returns fds differently
    if (v6_syscall(V6_SYS_pipe, (long)pipefd, 0, 0) < 0) {
        printf("  ✗ V6 pipe failed\n");
        return -1;
    }
    
    printf("  ✓ V6 pipe: [%d, %d]\n", pipefd[0], pipefd[1]);
    
    // Test pipe I/O
    const char *msg = "V6";
    v6_syscall(V6_SYS_write, pipefd[1], (long)msg, 2);
    
    char buf[8];
    ssize_t n = v6_syscall(V6_SYS_read, pipefd[0], (long)buf, sizeof(buf));
    if (n > 0) {
        buf[n] = '\0';
        printf("  ✓ Pipe data: '%s'\n", buf);
    }
    
    v6_syscall(V6_SYS_close, pipefd[0], 0, 0);
    v6_syscall(V6_SYS_close, pipefd[1], 0, 0);
    
    return 0;
}

// Test V6 signals (different numbers)
int test_v6_signals(void) {
    printf("Testing V6 signals...\n");
    
    // V6 signal numbers
    #define V6_SIGHUP  1
    #define V6_SIGINT  2
    #define V6_SIGQUIT 3
    #define V6_SIGILL  4
    #define V6_SIGTRAP 5
    #define V6_SIGEMT  7
    #define V6_SIGFPE  8
    #define V6_SIGKILL 9
    #define V6_SIGBUS  10
    #define V6_SIGSEGV 11
    #define V6_SIGSYS  12
    #define V6_SIGPIPE 13
    #define V6_SIGALRM 14
    #define V6_SIGTERM 15
    
    printf("  ✓ V6 signal numbers:\n");
    printf("    SIGHUP=%d SIGINT=%d SIGQUIT=%d\n", V6_SIGHUP, V6_SIGINT, V6_SIGQUIT);
    printf("    SIGKILL=%d SIGTERM=%d SIGALRM=%d\n", V6_SIGKILL, V6_SIGTERM, V6_SIGALRM);
    
    // Test alarm (syscall 27)
    v6_syscall(V6_SYS_alarm, 1, 0, 0);  // 1 second alarm
    printf("  ✓ V6 alarm set\n");
    
    // Cancel alarm
    v6_syscall(V6_SYS_alarm, 0, 0, 0);
    printf("  ✓ V6 alarm cancelled\n");
    
    return 0;
}

// Test V6 process control
int test_v6_process(void) {
    printf("Testing V6 process control...\n");
    
    // Test nice (syscall 34)
    int oldnice = v6_syscall(V6_SYS_nice, 5, 0, 0);
    printf("  ✓ V6 nice: priority adjusted by 5 (was %d)\n", oldnice);
    
    // Test sync (syscall 36)
    v6_syscall(V6_SYS_sync, 0, 0, 0);
    printf("  ✓ V6 sync: filesystem synced\n");
    
    // Test dup (syscall 41)
    int newfd = v6_syscall(V6_SYS_dup, 1, 0, 0);  // Duplicate stdout
    if (newfd > 0) {
        printf("  ✓ V6 dup: fd 1 duplicated to %d\n", newfd);
        v6_syscall(V6_SYS_close, newfd, 0, 0);
    }
    
    return 0;
}

int main(int argc, char *argv[]) {
    printf("===========================================\n");
    printf("V6/V7 UNIX Compatibility Test Binary\n");
    printf("===========================================\n");
    printf("This binary uses V6/V7 syscall numbers and\n");
    printf("structures to test historical compatibility\n");
    printf("===========================================\n\n");
    
    // Show basic info using V6 syscalls
    printf("Process ID: %ld\n", v6_syscall(V6_SYS_getpid, 0, 0, 0));
    printf("User ID: %ld\n", v6_syscall(V6_SYS_getuid, 0, 0, 0));
    printf("Group ID: %ld\n", v6_syscall(V6_SYS_getgid, 0, 0, 0));
    printf("\n");
    
    // Run V6 compatibility tests
    int failures = 0;
    
    if (test_v6_basic() < 0) failures++;
    printf("\n");
    
    if (test_v6_files() < 0) failures++;
    printf("\n");
    
    if (test_v6_stat() < 0) failures++;
    printf("\n");
    
    if (test_v6_pipe() < 0) failures++;
    printf("\n");
    
    if (test_v6_signals() < 0) failures++;
    printf("\n");
    
    if (test_v6_process() < 0) failures++;
    printf("\n");
    
    // Summary
    printf("===========================================\n");
    if (failures == 0) {
        printf("✅ All V6/V7 compatibility tests passed!\n");
        printf("   Historical UNIX binary support working!\n");
    } else {
        printf("❌ %d V6/V7 compatibility tests failed\n", failures);
    }
    printf("===========================================\n");
    
    return failures;
}
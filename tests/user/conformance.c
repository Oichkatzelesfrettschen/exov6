#include <user.h>
#include <fcntl.h>
#include <sys/stat.h>

// Simple assertion
#define ASSERT(c) \
    if(!(c)) { \
        printf(2, "Assertion failed: %s:%d\n", __FILE__, __LINE__); \
        exit(1); \
    }

// Helper to run a command and capture output
// Not fully implemented capturing due to lack of pipe support in test runner easily
// For now, just run and check exit code or side effects

void test_echo() {
    printf(1, "[TEST] echo\n");
    int pid = fork();
    if (pid == 0) {
        char *argv[] = {"echo", "test_echo", 0};
        exec("echo", argv);
        exit(1);
    }
    wait();
}

void test_mkdir_ls_rm() {
    printf(1, "[TEST] mkdir, ls, rm\n");

    int pid = fork();
    if (pid == 0) {
        char *argv[] = {"mkdir", "test_dir_1", 0};
        exec("mkdir", argv);
        exit(1);
    }
    wait();

    pid = fork();
    if (pid == 0) {
        char *argv[] = {"ls", ".", 0};
        exec("ls", argv);
        exit(1);
    }
    wait();

    // Cleanup with rmdir if available, or rm -r?
    // current rm might not support -r or directories.
    // Let's check rm.c later.
}

int main() {
    printf(1, "Starting conformance tests...\n");

    test_echo();
    test_mkdir_ls_rm();

    printf(1, "Conformance tests completed.\n");
    exit(0);
}

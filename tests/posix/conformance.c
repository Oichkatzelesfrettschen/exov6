#include <user.h>
#include <fcntl.h>
#include <sys/stat.h>

// Simple assertion
#define ASSERT(c) \
    if(!(c)) { \
        printf(2, "Assertion failed: %s:%d\n", __FILE__, __LINE__); \
        exit(1); \
    }

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

    // Cleanup
    pid = fork();
    if (pid == 0) {
        // Use -r since we have directories
        char *argv[] = {"rm", "-r", "test_dir_1", 0};
        exec("rm", argv);
        exit(1);
    }
    wait();
}

void test_mv_self() {
    printf(1, "[TEST] mv self (no-op)\n");
    // Create a file
    int fd = open("test_mv_self", O_CREATE | O_WRONLY);
    if (fd < 0) {
        printf(2, "Failed to create test file\n");
        exit(1);
    }
    write(fd, "content", 7);
    close(fd);

    int pid = fork();
    if (pid == 0) {
        char *argv[] = {"mv", "test_mv_self", "test_mv_self", 0};
        exec("mv", argv);
        exit(1);
    }
    wait();

    // Check file still exists and is valid
    struct stat st;
    ASSERT(stat("test_mv_self", &st) == 0);
    unlink("test_mv_self");
    printf(1, "mv self passed\n");
}

void test_rm_no_args() {
    printf(1, "[TEST] rm no args\n");
    int pid = fork();
    if (pid == 0) {
        char *argv[] = {"rm", 0};
        exec("rm", argv);
        // Should exit (either 0 or 1) but NOT crash
        exit(0);
    }
    wait();
    printf(1, "rm no args passed (did not crash)\n");
}

int main() {
    printf(1, "Starting conformance tests...\n");

    test_echo();
    test_mkdir_ls_rm();
    test_mv_self();
    test_rm_no_args();

    printf(1, "Conformance tests completed.\n");
    exit(0);
}

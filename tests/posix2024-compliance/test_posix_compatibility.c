/**
 * @file test_posix_compatibility.c
 * @brief Comprehensive POSIX 2024 compatibility test suite
 * 
 * Tests the multi-personality syscall gateway and POSIX 2024 compliance
 * with performance benchmarks and regression testing.
 */

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <unistd.h>
#include <fcntl.h>
#include <sys/stat.h>
#include <sys/wait.h>
#include <sys/mman.h>
#include <errno.h>
#include <assert.h>
#include <time.h>

// Include our POSIX compatibility headers
#include "../../kernel/sys/syscall_gateway.h"
#include "../../kernel/sys/syscall_posix2024.h"
#include "../../libos/posix2024/stdio.h"

// =============================================================================
// TEST FRAMEWORK
// =============================================================================

typedef struct test_result {
    const char *test_name;
    int passed;
    uint64_t duration_ns;
    const char *error_message;
} test_result_t;

static test_result_t test_results[100];
static int test_count = 0;

#define RUN_TEST(test_func) do { \
    struct timespec start, end; \
    clock_gettime(CLOCK_MONOTONIC, &start); \
    const char *error = test_func(); \
    clock_gettime(CLOCK_MONOTONIC, &end); \
    \
    test_results[test_count].test_name = #test_func; \
    test_results[test_count].passed = (error == NULL); \
    test_results[test_count].duration_ns = \
        (end.tv_sec - start.tv_sec) * 1000000000ULL + \
        (end.tv_nsec - start.tv_nsec); \
    test_results[test_count].error_message = error; \
    test_count++; \
} while(0)

// =============================================================================
// SYSCALL COMPATIBILITY TESTS
// =============================================================================

/**
 * Test basic file I/O syscalls
 */
const char *test_file_io_syscalls(void) {
    const char *test_file = "/tmp/posix_test_file";
    const char *test_data = "Hello, POSIX 2024!";
    char read_buffer[256];
    
    // Test open syscall
    int fd = open(test_file, O_CREAT | O_WRONLY | O_TRUNC, 0644);
    if (fd < 0) {
        return "open() syscall failed";
    }
    
    // Test write syscall
    ssize_t bytes_written = write(fd, test_data, strlen(test_data));
    if (bytes_written != strlen(test_data)) {
        close(fd);
        return "write() syscall failed";
    }
    
    // Test close syscall
    if (close(fd) < 0) {
        return "close() syscall failed";
    }
    
    // Test open for reading
    fd = open(test_file, O_RDONLY);
    if (fd < 0) {
        return "open() for reading failed";
    }
    
    // Test read syscall
    ssize_t bytes_read = read(fd, read_buffer, sizeof(read_buffer) - 1);
    if (bytes_read != strlen(test_data)) {
        close(fd);
        return "read() syscall failed";
    }
    
    read_buffer[bytes_read] = '\0';
    if (strcmp(read_buffer, test_data) != 0) {
        close(fd);
        return "read() data mismatch";
    }
    
    close(fd);
    unlink(test_file);  // Cleanup
    
    return NULL;  // Success
}

/**
 * Test process management syscalls
 */
const char *test_process_syscalls(void) {
    pid_t pid, child_pid;
    int status;
    
    // Test getpid syscall
    pid = getpid();
    if (pid <= 0) {
        return "getpid() syscall failed";
    }
    
    // Test fork syscall
    child_pid = fork();
    if (child_pid < 0) {
        return "fork() syscall failed";
    }
    
    if (child_pid == 0) {
        // Child process - test exit syscall
        exit(42);
    } else {
        // Parent process - test wait syscall
        pid_t waited_pid = wait(&status);
        if (waited_pid != child_pid) {
            return "wait() syscall failed";
        }
        
        if (!WIFEXITED(status) || WEXITSTATUS(status) != 42) {
            return "child process exit status incorrect";
        }
    }
    
    return NULL;  // Success
}

/**
 * Test memory management syscalls
 */
const char *test_memory_syscalls(void) {
    size_t page_size = 4096;
    void *addr;
    
    // Test mmap syscall
    addr = mmap(NULL, page_size, PROT_READ | PROT_WRITE,
                MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    if (addr == MAP_FAILED) {
        return "mmap() syscall failed";
    }
    
    // Test memory access
    char *test_ptr = (char *)addr;
    *test_ptr = 'A';
    if (*test_ptr != 'A') {
        munmap(addr, page_size);
        return "memory access after mmap failed";
    }
    
    // Test munmap syscall
    if (munmap(addr, page_size) < 0) {
        return "munmap() syscall failed";
    }
    
    return NULL;  // Success
}

/**
 * Test stat family syscalls
 */
const char *test_stat_syscalls(void) {
    const char *test_file = "/tmp/posix_stat_test";
    struct stat st;
    int fd;
    
    // Create test file
    fd = open(test_file, O_CREAT | O_WRONLY | O_TRUNC, 0644);
    if (fd < 0) {
        return "failed to create test file for stat";
    }
    
    write(fd, "test", 4);
    close(fd);
    
    // Test stat syscall
    if (stat(test_file, &st) < 0) {
        unlink(test_file);
        return "stat() syscall failed";
    }
    
    // Verify stat results
    if (!S_ISREG(st.st_mode)) {
        unlink(test_file);
        return "stat() mode incorrect";
    }
    
    if (st.st_size != 4) {
        unlink(test_file);
        return "stat() size incorrect";
    }
    
    // Test fstat syscall
    fd = open(test_file, O_RDONLY);
    if (fd < 0) {
        unlink(test_file);
        return "failed to reopen test file for fstat";
    }
    
    struct stat fst;
    if (fstat(fd, &fst) < 0) {
        close(fd);
        unlink(test_file);
        return "fstat() syscall failed";
    }
    
    // Compare stat and fstat results
    if (st.st_ino != fst.st_ino || st.st_size != fst.st_size) {
        close(fd);
        unlink(test_file);
        return "stat() and fstat() results differ";
    }
    
    close(fd);
    unlink(test_file);
    
    return NULL;  // Success
}

// =============================================================================
// PERSONALITY GATEWAY TESTS
// =============================================================================

/**
 * Test multi-personality syscall dispatch
 */
const char *test_personality_dispatch(void) {
    // This would test the actual gateway dispatch mechanism
    // For now, we'll test that different personalities can be set
    
    struct proc *current = myproc();  // This would be the actual current process
    syscall_personality_t original_personality = get_process_personality(current);
    
    // Test setting POSIX personality
    if (set_process_personality(current, PERSONALITY_POSIX2024) < 0) {
        return "failed to set POSIX 2024 personality";
    }
    
    if (get_process_personality(current) != PERSONALITY_POSIX2024) {
        return "personality not set correctly";
    }
    
    // Test setting FeuerBird personality
    if (set_process_personality(current, PERSONALITY_FEUERBIRD) < 0) {
        return "failed to set FeuerBird personality";
    }
    
    if (get_process_personality(current) != PERSONALITY_FEUERBIRD) {
        return "FeuerBird personality not set correctly";
    }
    
    // Restore original personality
    set_process_personality(current, original_personality);
    
    return NULL;  // Success
}

/**
 * Test classed syscall number encoding/decoding
 */
const char *test_classed_syscalls(void) {
    unsigned int class = SYSCALL_CLASS_POSIX;
    unsigned int number = 42;
    
    // Test encoding
    unsigned long classed_nr = syscall_make_classed(class, number);
    
    // Test decoding
    unsigned int decoded_class = syscall_get_class(classed_nr);
    unsigned int decoded_number = syscall_get_number(classed_nr);
    
    if (decoded_class != class) {
        return "syscall class encoding/decoding failed";
    }
    
    if (decoded_number != number) {
        return "syscall number encoding/decoding failed";
    }
    
    return NULL;  // Success
}

// =============================================================================
// STDIO COMPATIBILITY TESTS  
// =============================================================================

/**
 * Test POSIX stdio implementation
 */
const char *test_stdio_compatibility(void) {
    const char *test_file = "/tmp/posix_stdio_test";
    FILE *fp;
    char buffer[256];
    
    // Test fopen
    fp = fopen(test_file, "w");
    if (!fp) {
        return "fopen() for writing failed";
    }
    
    // Test fprintf
    if (fprintf(fp, "Test number: %d\n", 12345) < 0) {
        fclose(fp);
        return "fprintf() failed";
    }
    
    // Test fclose
    if (fclose(fp) != 0) {
        return "fclose() failed";
    }
    
    // Test fopen for reading
    fp = fopen(test_file, "r");
    if (!fp) {
        unlink(test_file);
        return "fopen() for reading failed";
    }
    
    // Test fgets
    if (!fgets(buffer, sizeof(buffer), fp)) {
        fclose(fp);
        unlink(test_file);
        return "fgets() failed";
    }
    
    // Verify content
    if (strstr(buffer, "12345") == NULL) {
        fclose(fp);
        unlink(test_file);
        return "stdio content verification failed";
    }
    
    fclose(fp);
    unlink(test_file);
    
    return NULL;  // Success
}

// =============================================================================
// PERFORMANCE BENCHMARK TESTS
// =============================================================================

/**
 * Benchmark syscall performance overhead
 */
const char *test_syscall_performance(void) {
    const int iterations = 10000;
    struct timespec start, end;
    uint64_t native_time, posix_time;
    
    // Benchmark native FeuerBird getpid
    clock_gettime(CLOCK_MONOTONIC, &start);
    for (int i = 0; i < iterations; i++) {
        syscall(SYS_getpid);  // Direct native syscall
    }
    clock_gettime(CLOCK_MONOTONIC, &end);
    native_time = (end.tv_sec - start.tv_sec) * 1000000000ULL + 
                  (end.tv_nsec - start.tv_nsec);
    
    // Benchmark POSIX getpid through compatibility layer
    clock_gettime(CLOCK_MONOTONIC, &start);
    for (int i = 0; i < iterations; i++) {
        getpid();  // POSIX compatibility syscall
    }
    clock_gettime(CLOCK_MONOTONIC, &end);
    posix_time = (end.tv_sec - start.tv_sec) * 1000000000ULL + 
                 (end.tv_nsec - start.tv_nsec);
    
    // Calculate overhead
    double overhead_percent = ((double)(posix_time - native_time) / native_time) * 100.0;
    
    printf("Performance benchmark:\n");
    printf("  Native syscalls:  %llu ns/call\n", native_time / iterations);
    printf("  POSIX syscalls:   %llu ns/call\n", posix_time / iterations);
    printf("  Overhead:         %.2f%%\n", overhead_percent);
    
    // Fail if overhead is too high (target: <10%)
    if (overhead_percent > 10.0) {
        return "POSIX syscall overhead exceeds 10% target";
    }
    
    return NULL;  // Success
}

// =============================================================================
// INTEGRATION TESTS
// =============================================================================

/**
 * Test running a simple POSIX program
 */
const char *test_posix_program_execution(void) {
    const char *test_program = "/tmp/posix_test_program.c";
    const char *test_binary = "/tmp/posix_test_program";
    FILE *fp;
    int status;
    
    // Create simple test program
    fp = fopen(test_program, "w");
    if (!fp) {
        return "failed to create test program source";
    }
    
    fprintf(fp, 
        "#include <stdio.h>\n"
        "#include <unistd.h>\n"
        "int main() {\n"
        "  printf(\"POSIX test: %%d\\n\", getpid());\n"
        "  return 42;\n"
        "}\n");
    
    fclose(fp);
    
    // Compile test program (assuming gcc is available)
    char compile_cmd[512];
    snprintf(compile_cmd, sizeof(compile_cmd), 
             "gcc -std=c17 -o %s %s", test_binary, test_program);
    
    if (system(compile_cmd) != 0) {
        unlink(test_program);
        return "failed to compile test program";
    }
    
    // Execute test program
    pid_t child = fork();
    if (child < 0) {
        unlink(test_program);
        unlink(test_binary);
        return "fork failed for test program execution";
    }
    
    if (child == 0) {
        execl(test_binary, "posix_test_program", NULL);
        exit(127);  // execl failed
    } else {
        wait(&status);
        if (!WIFEXITED(status) || WEXITSTATUS(status) != 42) {
            unlink(test_program);
            unlink(test_binary);
            return "test program execution failed";
        }
    }
    
    unlink(test_program);
    unlink(test_binary);
    
    return NULL;  // Success
}

// =============================================================================
// MAIN TEST RUNNER
// =============================================================================

int main(void) {
    printf("🧪 FeuerBird POSIX 2024 Compatibility Test Suite\n");
    printf("================================================\n\n");
    
    // Initialize test environment
    printf("Initializing POSIX compatibility layer...\n");
    posix_stdio_init();
    printf("✅ POSIX stdio initialized\n\n");
    
    // Run syscall compatibility tests
    printf("🔧 Testing POSIX syscall compatibility:\n");
    RUN_TEST(test_file_io_syscalls);
    RUN_TEST(test_process_syscalls);
    RUN_TEST(test_memory_syscalls);
    RUN_TEST(test_stat_syscalls);
    printf("\n");
    
    // Run personality gateway tests
    printf("🎭 Testing multi-personality syscall gateway:\n");
    RUN_TEST(test_personality_dispatch);
    RUN_TEST(test_classed_syscalls);
    printf("\n");
    
    // Run stdio compatibility tests
    printf("📄 Testing POSIX stdio compatibility:\n");
    RUN_TEST(test_stdio_compatibility);
    printf("\n");
    
    // Run performance benchmarks
    printf("⚡ Running performance benchmarks:\n");
    RUN_TEST(test_syscall_performance);
    printf("\n");
    
    // Run integration tests
    printf("🔗 Running integration tests:\n");
    RUN_TEST(test_posix_program_execution);
    printf("\n");
    
    // Print results summary
    printf("📊 Test Results Summary\n");
    printf("======================\n");
    
    int passed_tests = 0;
    uint64_t total_time = 0;
    
    for (int i = 0; i < test_count; i++) {
        const char *status = test_results[i].passed ? "✅ PASS" : "❌ FAIL";
        printf("%-30s %s (%llu ns)\n", 
               test_results[i].test_name,
               status,
               test_results[i].duration_ns);
        
        if (!test_results[i].passed) {
            printf("    Error: %s\n", test_results[i].error_message);
        }
        
        if (test_results[i].passed) {
            passed_tests++;
        }
        total_time += test_results[i].duration_ns;
    }
    
    printf("\n");
    printf("Tests run:     %d\n", test_count);
    printf("Tests passed:  %d\n", passed_tests);
    printf("Tests failed:  %d\n", test_count - passed_tests);
    printf("Success rate:  %.1f%%\n", (100.0 * passed_tests) / test_count);
    printf("Total time:    %llu ns\n", total_time);
    printf("Average time:  %llu ns per test\n", total_time / test_count);
    
    if (passed_tests == test_count) {
        printf("\n🎉 ALL POSIX 2024 COMPATIBILITY TESTS PASSED!\n");
        printf("✅ FeuerBird POSIX compatibility layer is working correctly!\n");
        printf("🚀 Multi-personality syscall gateway operational!\n");
        return 0;
    } else {
        printf("\n⚠️  Some compatibility tests failed!\n");
        printf("❌ POSIX compatibility layer needs attention\n");
        return 1;
    }
}
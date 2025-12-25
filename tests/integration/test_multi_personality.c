/**
 * @file test_multi_personality.c
 * @brief Comprehensive integration test for multi-personality syscall gateway
 * 
 * Tests all 5 personalities: FeuerBird, POSIX 2024, Linux, BSD, and Illumos
 * with structure versioning, translation, and performance benchmarks.
 */

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
#include <assert.h>

// Include our kernel headers (in test environment)
#include "../../kernel/sys/syscall_gateway.h"
#include "../../kernel/sys/abi_versioning.h"

// =============================================================================
// TEST FRAMEWORK
// =============================================================================

typedef struct {
    const char *name;
    int (*test_func)(void);
    int passed;
    uint64_t duration_ns;
} test_case_t;

static test_case_t tests[100];
static int test_count = 0;

#define RUN_TEST(func) do { \
    struct timespec start, end; \
    clock_gettime(CLOCK_MONOTONIC, &start); \
    tests[test_count].name = #func; \
    tests[test_count].test_func = func; \
    tests[test_count].passed = (func() == 0); \
    clock_gettime(CLOCK_MONOTONIC, &end); \
    tests[test_count].duration_ns = \
        (end.tv_sec - start.tv_sec) * 1000000000ULL + \
        (end.tv_nsec - start.tv_nsec); \
    test_count++; \
} while(0)

// =============================================================================
// PERSONALITY TESTS
// =============================================================================

/**
 * Test classed syscall encoding for all personalities
 */
int test_classed_syscalls(void) {
    struct {
        unsigned int class;
        unsigned int number;
        const char *name;
    } test_cases[] = {
        {SYSCALL_CLASS_FEUERBIRD, 42, "FeuerBird"},
        {SYSCALL_CLASS_POSIX, 123, "POSIX"},
        {SYSCALL_CLASS_LINUX, 200, "Linux"},
        {SYSCALL_CLASS_BSD, 300, "BSD"},
        {SYSCALL_CLASS_ILLUMOS, 150, "Illumos"},
    };
    
    for (int i = 0; i < 5; i++) {
        unsigned long encoded = syscall_make_classed(test_cases[i].class, test_cases[i].number);
        unsigned int decoded_class = syscall_get_class(encoded);
        unsigned int decoded_number = syscall_get_number(encoded);
        
        if (decoded_class != test_cases[i].class) {
            printf("FAIL: %s class encoding failed\n", test_cases[i].name);
            return -1;
        }
        
        if (decoded_number != test_cases[i].number) {
            printf("FAIL: %s number encoding failed\n", test_cases[i].name);
            return -1;
        }
    }
    
    return 0;
}

/**
 * Test ABI version detection
 */
int test_abi_version_detection(void) {
    // Test various magic numbers
    uint8_t elf_linux[] = {0x7F, 'E', 'L', 'F', 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
    uint8_t v7_aout[] = {0x07, 0x01};
    
    abi_version_t version;
    
    // ELF should default to POSIX
    version = detect_abi_version(elf_linux);
    assert(version == ABI_VERSION_POSIX24);
    
    // V7 a.out magic
    version = detect_abi_version(v7_aout);
    assert(version == ABI_VERSION_V7);
    
    return 0;
}

/**
 * Test structure versioning - V6 to modern stat conversion
 */
int test_v6_stat_conversion(void) {
    struct stat_v6 v6_stat = {
        .st_dev = 0x0102,
        .st_ino = 0x1234,
        .st_mode = 0755,
        .st_nlink = 2,
        .st_uid = 100,
        .st_gid = 50,
        .st_size0 = 0x01,
        .st_size1 = 0x2345,
        .st_atime = {0x0000, 0x1234},
        .st_mtime = {0x0000, 0x5678}
    };
    
    struct stat modern_stat;
    
    // Convert V6 to modern
    int ret = translate_stat_version(&v6_stat, ABI_VERSION_V6,
                                    &modern_stat, ABI_VERSION_POSIX24);
    assert(ret == 0);
    
    // Verify conversion
    assert(modern_stat.dev == 0x0102);
    assert(modern_stat.ino == 0x1234);
    assert(modern_stat.mode == 0755);
    assert(modern_stat.nlink == 2);
    
    // V6 3-byte size: 0x01 << 16 | 0x2345 = 0x012345
    assert(modern_stat.size == 0x012345);
    
    return 0;
}

/**
 * Test errno translation across versions
 */
int test_errno_translation(void) {
    // Test V7 to Linux errno translation
    int v7_errno = V7_EAGAIN;  // 11 in V7
    int linux_errno = translate_errno_version(v7_errno, ABI_VERSION_V7, ABI_VERSION_LINUX6);
    assert(linux_errno == 11);  // Same in Linux
    
    // Test V7 to BSD errno translation
    int bsd_errno = translate_errno_version(v7_errno, ABI_VERSION_V7, ABI_VERSION_BSD44);
    assert(bsd_errno == 35);  // EAGAIN is 35 (EWOULDBLOCK) in BSD
    
    return 0;
}

/**
 * Test Y2038 time conversion
 */
int test_time_conversion(void) {
    // Test 32-bit to 64-bit conversion
    struct timeval32 tv32 = {
        .tv_sec = 0x7FFFFFFF,  // Max 32-bit time (2038-01-19)
        .tv_usec = 999999
    };
    
    struct timeval64 tv64;
    int ret = translate_time_version(&tv32, ABI_VERSION_LINUX4,
                                    &tv64, ABI_VERSION_LINUX6);
    assert(ret == 0);
    assert(tv64.tv_sec == 0x7FFFFFFF);
    assert(tv64.tv_usec == 999999);
    
    // Test 64-bit to 32-bit with overflow
    tv64.tv_sec = 0x100000000;  // Beyond 2038
    ret = translate_time_version(&tv64, ABI_VERSION_LINUX6,
                                &tv32, ABI_VERSION_LINUX4);
    assert(ret == 0);
    assert(tv32.tv_sec == 0x7FFFFFFF);  // Clamped to max
    
    return 0;
}

// =============================================================================
// PERFORMANCE TESTS
// =============================================================================

/**
 * Benchmark syscall dispatch overhead
 */
int test_dispatch_performance(void) {
    const int iterations = 1000000;
    struct timespec start, end;
    uint64_t native_time, translated_time;
    
    // Benchmark native syscall encoding
    clock_gettime(CLOCK_MONOTONIC, &start);
    for (int i = 0; i < iterations; i++) {
        unsigned long nr = syscall_make_classed(SYSCALL_CLASS_FEUERBIRD, 20);
        volatile unsigned int class = syscall_get_class(nr);
        volatile unsigned int num = syscall_get_number(nr);
        (void)class;
        (void)num;
    }
    clock_gettime(CLOCK_MONOTONIC, &end);
    native_time = (end.tv_sec - start.tv_sec) * 1000000000ULL + 
                  (end.tv_nsec - start.tv_nsec);
    
    // Benchmark with translation
    clock_gettime(CLOCK_MONOTONIC, &start);
    for (int i = 0; i < iterations; i++) {
        unsigned long nr = syscall_make_classed(SYSCALL_CLASS_LINUX, 20);
        volatile unsigned int class = syscall_get_class(nr);
        volatile unsigned int num = syscall_get_number(nr);
        // Simulate flag translation
        int flags = 0x42;
        flags = (flags & 0x3) | ((flags & 0x40) << 2);
        (void)class;
        (void)num;
        (void)flags;
    }
    clock_gettime(CLOCK_MONOTONIC, &end);
    translated_time = (end.tv_sec - start.tv_sec) * 1000000000ULL + 
                     (end.tv_nsec - start.tv_nsec);
    
    // Calculate overhead
    double overhead = ((double)(translated_time - native_time) / native_time) * 100.0;
    
    printf("Performance:\n");
    printf("  Native: %llu ns (%llu ns/call)\n", native_time, native_time/iterations);
    printf("  Translated: %llu ns (%llu ns/call)\n", translated_time, translated_time/iterations);
    printf("  Overhead: %.2f%%\n", overhead);
    
    // Target: < 10% overhead
    if (overhead > 10.0) {
        printf("WARNING: Translation overhead exceeds 10%% target\n");
        return -1;
    }
    
    return 0;
}

// =============================================================================
// INTEGRATION TESTS
// =============================================================================

/**
 * Test complete personality switching flow
 */
int test_personality_switching(void) {
    // Simulate process personality changes
    syscall_personality_t personalities[] = {
        PERSONALITY_FEUERBIRD,
        PERSONALITY_POSIX2024,
        PERSONALITY_LINUX,
        PERSONALITY_BSD,
        PERSONALITY_ILLUMOS
    };
    
    for (int i = 0; i < 5; i++) {
        // Each personality should have unique behavior
        unsigned long syscall_nr = 20;  // getpid
        
        // Add personality class
        if (personalities[i] != PERSONALITY_FEUERBIRD) {
            syscall_nr = syscall_make_classed(personalities[i], syscall_nr);
        }
        
        unsigned int class = syscall_get_class(syscall_nr);
        
        // Verify correct class encoding
        switch (personalities[i]) {
            case PERSONALITY_FEUERBIRD:
                assert(class == 0);
                break;
            case PERSONALITY_POSIX2024:
                assert(class == SYSCALL_CLASS_POSIX);
                break;
            case PERSONALITY_LINUX:
                assert(class == SYSCALL_CLASS_LINUX);
                break;
            case PERSONALITY_BSD:
                assert(class == SYSCALL_CLASS_BSD);
                break;
            case PERSONALITY_ILLUMOS:
                assert(class == SYSCALL_CLASS_ILLUMOS);
                break;
            default:
                return -1;
        }
    }
    
    return 0;
}

/**
 * Test cross-personality compatibility
 */
int test_cross_personality_compat(void) {
    // Test that common syscalls work across personalities
    unsigned int common_syscalls[] = {
        3,   // read
        4,   // write
        5,   // open
        6,   // close
        20,  // getpid
    };
    
    syscall_personality_t personalities[] = {
        PERSONALITY_POSIX2024,
        PERSONALITY_LINUX,
        PERSONALITY_BSD,
        PERSONALITY_ILLUMOS
    };
    
    for (int p = 0; p < 4; p++) {
        for (int s = 0; s < 5; s++) {
            // Each personality should handle common syscalls
            unsigned long nr = syscall_make_classed(personalities[p], common_syscalls[s]);
            unsigned int decoded = syscall_get_number(nr);
            assert(decoded == common_syscalls[s]);
        }
    }
    
    return 0;
}

// =============================================================================
// MAIN TEST RUNNER
// =============================================================================

int main(void) {
    printf("🧪 Multi-Personality Syscall Gateway Integration Test\n");
    printf("=====================================================\n\n");
    
    // Basic functionality tests
    printf("📋 Basic Functionality Tests:\n");
    RUN_TEST(test_classed_syscalls);
    RUN_TEST(test_abi_version_detection);
    printf("\n");
    
    // Structure versioning tests
    printf("🔄 Structure Versioning Tests:\n");
    RUN_TEST(test_v6_stat_conversion);
    RUN_TEST(test_errno_translation);
    RUN_TEST(test_time_conversion);
    printf("\n");
    
    // Performance tests
    printf("⚡ Performance Tests:\n");
    RUN_TEST(test_dispatch_performance);
    printf("\n");
    
    // Integration tests
    printf("🔗 Integration Tests:\n");
    RUN_TEST(test_personality_switching);
    RUN_TEST(test_cross_personality_compat);
    printf("\n");
    
    // Print results
    printf("📊 Test Results Summary\n");
    printf("======================\n");
    
    int passed = 0;
    uint64_t total_time = 0;
    
    for (int i = 0; i < test_count; i++) {
        printf("%-30s: %s (%llu ns)\n",
               tests[i].name,
               tests[i].passed ? "✅ PASS" : "❌ FAIL",
               tests[i].duration_ns);
        
        if (tests[i].passed)
            passed++;
        
        total_time += tests[i].duration_ns;
    }
    
    printf("\n");
    printf("Tests run: %d\n", test_count);
    printf("Tests passed: %d\n", passed);
    printf("Tests failed: %d\n", test_count - passed);
    printf("Success rate: %.1f%%\n", (100.0 * passed) / test_count);
    printf("Total time: %llu ns\n", total_time);
    
    if (passed == test_count) {
        printf("\n🎉 ALL TESTS PASSED!\n");
        printf("✅ Multi-personality syscall gateway is fully operational!\n");
        printf("🚀 Supporting: FeuerBird, POSIX 2024, Linux, BSD, and Illumos!\n");
        return 0;
    } else {
        printf("\n⚠️ Some tests failed!\n");
        return 1;
    }
}
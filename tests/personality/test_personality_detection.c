/**
 * @file test_personality_detection.c
 * @brief Integration test for ELF personality detection
 * 
 * This test validates that our kernel correctly detects and sets
 * process personalities based on ELF headers, notes, and interpreters.
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <fcntl.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <errno.h>

// Include kernel headers for testing
#include "../../kernel/sys/syscall_gateway.h"
#include "../../kernel/sys/elf_personality.h"
#include "../../kernel/fs.h"
#include "../../kernel/file.h"
#include "../../kernel/proc.h"

// Test result structure
typedef struct {
    const char *binary_path;
    const char *description;
    syscall_personality_t expected_personality;
    int detected_personality;
    int passed;
} test_result_t;

// Global test results
static test_result_t test_results[10];
static int num_tests = 0;

/**
 * Test personality detection for a binary
 */
int test_binary_personality(const char *binary_path, syscall_personality_t expected) {
    struct file *f;
    struct inode *ip;
    syscall_personality_t detected;
    
    // Open the binary file
    if ((ip = namei(binary_path)) == 0) {
        printf("  ✗ Cannot find %s\n", binary_path);
        return -1;
    }
    
    if ((f = filealloc()) == 0) {
        iunlockput(ip);
        printf("  ✗ Cannot allocate file\n");
        return -1;
    }
    
    f->type = FD_INODE;
    f->ip = ip;
    f->off = 0;
    f->readable = 1;
    f->writable = 0;
    
    // Detect personality from ELF
    detected = detect_elf_personality(f);
    
    // Clean up
    fileclose(f);
    
    // Check result
    if (detected == expected) {
        printf("  ✅ %s: Correctly detected as %s\n", 
               binary_path, get_personality_name(detected));
        return 0;
    } else {
        printf("  ❌ %s: Expected %s, got %s\n",
               binary_path, 
               get_personality_name(expected),
               get_personality_name(detected));
        return -1;
    }
}

/**
 * Test process personality setup
 */
int test_process_personality_setup(const char *binary_path, syscall_personality_t expected) {
    struct proc *p;
    struct file *f;
    struct inode *ip;
    int ret;
    
    // Allocate a test process
    p = allocproc();
    if (!p) {
        printf("  ✗ Cannot allocate process\n");
        return -1;
    }
    
    // Open binary
    if ((ip = namei(binary_path)) == 0) {
        printf("  ✗ Cannot find %s\n", binary_path);
        return -1;
    }
    
    if ((f = filealloc()) == 0) {
        iunlockput(ip);
        printf("  ✗ Cannot allocate file\n");
        return -1;
    }
    
    f->type = FD_INODE;
    f->ip = ip;
    f->off = 0;
    f->readable = 1;
    
    // Set up process personality
    ret = setup_process_personality(p, f);
    
    if (ret == 0 && p->personality == expected) {
        printf("  ✅ Process personality setup succeeded\n");
        
        // Check personality-specific flags
        switch (expected) {
            case PERSONALITY_LINUX:
                if (p->flags & PROC_LINUX_COMPAT) {
                    printf("     PROC_LINUX_COMPAT flag set\n");
                }
                break;
            case PERSONALITY_BSD:
                if (p->flags & PROC_BSD_COMPAT) {
                    printf("     PROC_BSD_COMPAT flag set\n");
                }
                break;
            case PERSONALITY_ILLUMOS:
                if (p->flags & PROC_ILLUMOS_COMPAT) {
                    printf("     PROC_ILLUMOS_COMPAT flag set\n");
                }
                break;
            case PERSONALITY_POSIX2024:
                if (p->flags & PROC_POSIX_STRICT) {
                    printf("     PROC_POSIX_STRICT flag set\n");
                }
                break;
            default:
                break;
        }
    } else {
        printf("  ❌ Process personality setup failed\n");
        ret = -1;
    }
    
    // Clean up
    fileclose(f);
    
    return ret;
}

/**
 * Test syscall routing based on personality
 */
int test_personality_syscall_routing(void) {
    printf("\n🔄 Testing Syscall Routing by Personality\n");
    printf("=========================================\n");
    
    // Test Linux syscall routing
    unsigned long linux_getpid = syscall_make_classed(SYSCALL_CLASS_LINUX, 39);  // Linux getpid
    printf("Linux getpid encoding: 0x%lx\n", linux_getpid);
    printf("  Class: %u, Number: %u\n", 
           syscall_get_class(linux_getpid),
           syscall_get_number(linux_getpid));
    
    // Test BSD syscall routing
    unsigned long bsd_getpid = syscall_make_classed(SYSCALL_CLASS_BSD, 20);  // BSD getpid
    printf("BSD getpid encoding: 0x%lx\n", bsd_getpid);
    printf("  Class: %u, Number: %u\n",
           syscall_get_class(bsd_getpid),
           syscall_get_number(bsd_getpid));
    
    // Test Illumos syscall routing
    unsigned long illumos_zone = syscall_make_classed(SYSCALL_CLASS_ILLUMOS, 227);  // zone syscall
    printf("Illumos zone encoding: 0x%lx\n", illumos_zone);
    printf("  Class: %u, Number: %u\n",
           syscall_get_class(illumos_zone),
           syscall_get_number(illumos_zone));
    
    return 0;
}

/**
 * Test personality switching at runtime
 */
int test_personality_switching(void) {
    printf("\n🔄 Testing Runtime Personality Switching\n");
    printf("=========================================\n");
    
    struct proc *p = allocproc();
    if (!p) {
        printf("  ✗ Cannot allocate process\n");
        return -1;
    }
    
    // Start with native personality
    p->personality = PERSONALITY_FEUERBIRD;
    p->flags = 0;
    
    // Switch to Linux
    if (switch_process_personality(p, PERSONALITY_LINUX) == 0) {
        printf("  ✅ Switched to Linux personality\n");
        if (p->flags & PROC_LINUX_COMPAT) {
            printf("     PROC_LINUX_COMPAT flag set\n");
        }
    }
    
    // Switch to BSD
    if (switch_process_personality(p, PERSONALITY_BSD) == 0) {
        printf("  ✅ Switched to BSD personality\n");
        if (p->flags & PROC_BSD_COMPAT) {
            printf("     PROC_BSD_COMPAT flag set\n");
        }
        if (!(p->flags & PROC_LINUX_COMPAT)) {
            printf("     PROC_LINUX_COMPAT flag cleared\n");
        }
    }
    
    // Try invalid switch to native after process started
    p->state = RUNNABLE;
    if (switch_process_personality(p, PERSONALITY_FEUERBIRD) == -EPERM) {
        printf("  ✅ Correctly denied switch to native after start\n");
    }
    
    return 0;
}

/**
 * Run integration test with real binaries
 */
int test_with_real_binaries(void) {
    printf("\n📦 Testing with Real Binaries\n");
    printf("=========================================\n");
    
    struct {
        const char *path;
        syscall_personality_t expected;
        const char *description;
    } test_binaries[] = {
        {"binaries/test_linux", PERSONALITY_LINUX, "Linux ELF with GNU note"},
        {"binaries/test_bsd", PERSONALITY_BSD, "BSD ELF with FreeBSD note"},
        {"binaries/test_illumos", PERSONALITY_ILLUMOS, "Illumos ELF with Solaris note"},
        {"binaries/test_posix", PERSONALITY_POSIX2024, "POSIX 2024 compliant ELF"},
        {"binaries/test_feuerbird", PERSONALITY_FEUERBIRD, "Native FeuerBird ELF"},
        {"binaries/test_v6", PERSONALITY_POSIX2024, "V6/V7 compatibility test"},
        {NULL, 0, NULL}
    };
    
    int failures = 0;
    
    for (int i = 0; test_binaries[i].path != NULL; i++) {
        printf("\nTesting: %s\n", test_binaries[i].description);
        printf("Binary: %s\n", test_binaries[i].path);
        
        // Check if binary exists
        if (access(test_binaries[i].path, F_OK) != 0) {
            printf("  ⚠️ Binary not found (run build_test_binaries.sh first)\n");
            continue;
        }
        
        // Test personality detection
        if (test_binary_personality(test_binaries[i].path, 
                                   test_binaries[i].expected) < 0) {
            failures++;
        }
        
        // Test process setup
        if (test_process_personality_setup(test_binaries[i].path,
                                          test_binaries[i].expected) < 0) {
            failures++;
        }
        
        // Record result
        test_results[num_tests].binary_path = test_binaries[i].path;
        test_results[num_tests].description = test_binaries[i].description;
        test_results[num_tests].expected_personality = test_binaries[i].expected;
        test_results[num_tests].passed = (failures == 0);
        num_tests++;
    }
    
    return failures;
}

/**
 * Print test summary
 */
void print_summary(void) {
    printf("\n📊 Test Summary\n");
    printf("=========================================\n");
    
    int passed = 0;
    int failed = 0;
    
    for (int i = 0; i < num_tests; i++) {
        printf("%-30s: %s\n",
               test_results[i].description,
               test_results[i].passed ? "✅ PASSED" : "❌ FAILED");
        
        if (test_results[i].passed)
            passed++;
        else
            failed++;
    }
    
    printf("\n");
    printf("Total tests: %d\n", num_tests);
    printf("Passed: %d\n", passed);
    printf("Failed: %d\n", failed);
    printf("Success rate: %.1f%%\n", 
           num_tests > 0 ? (100.0 * passed / num_tests) : 0);
}

int main(int argc, char *argv[]) {
    printf("🧪 Personality Detection Integration Test\n");
    printf("=========================================\n");
    printf("Testing ELF-based personality detection\n");
    printf("and multi-personality syscall gateway\n");
    printf("=========================================\n");
    
    int failures = 0;
    
    // Test syscall routing
    failures += test_personality_syscall_routing();
    
    // Test personality switching
    failures += test_personality_switching();
    
    // Test with real binaries
    failures += test_with_real_binaries();
    
    // Print summary
    print_summary();
    
    if (failures == 0) {
        printf("\n🎉 All personality detection tests passed!\n");
        printf("✅ Multi-personality gateway is working!\n");
        return 0;
    } else {
        printf("\n⚠️ %d tests failed!\n", failures);
        return 1;
    }
}
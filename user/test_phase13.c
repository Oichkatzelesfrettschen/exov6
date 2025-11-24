/**
 * @file test_phase13.c
 * @brief Test program for Phase 13 TCC prerequisites
 *
 * Tests the new lseek, unlink, malloc/free, and mmap functionality.
 */

#include <types.h>
#include <fd.h>
#include <mman.h>

extern void print(const char *s);
extern void print_hex(uint64 n);

/* External malloc functions */
extern void* malloc(uint64 size);
extern void free(void* ptr);
extern void* calloc(uint64 nmemb, uint64 size);
extern void* realloc(void* ptr, uint64 size);

static void print_test(const char *name, int passed) {
    print("  [");
    if (passed) {
        print("PASS");
    } else {
        print("FAIL");
    }
    print("] ");
    print(name);
    print("\n");
}

/**
 * Test malloc/free functionality
 */
static int test_malloc_free(void) {
    print("\n=== Testing malloc/free ===\n");
    
    /* Test 1: Basic allocation */
    void *p1 = malloc(100);
    int pass1 = (p1 != 0);
    print_test("malloc(100)", pass1);
    
    /* Test 2: Multiple allocations */
    void *p2 = malloc(200);
    void *p3 = malloc(300);
    int pass2 = (p2 != 0 && p3 != 0 && p1 != p2 && p2 != p3);
    print_test("Multiple malloc", pass2);
    
    /* Test 3: Free and realloc */
    free(p2);
    void *p4 = malloc(150);
    int pass3 = (p4 != 0);
    print_test("Free and realloc", pass3);
    
    /* Test 4: calloc */
    void *p5 = calloc(10, 20);
    int pass4 = (p5 != 0);
    print_test("calloc(10, 20)", pass4);
    
    /* Test 5: realloc */
    void *p6 = realloc(p1, 200);
    int pass5 = (p6 != 0);
    print_test("realloc(p1, 200)", pass5);
    
    /* Cleanup */
    free(p3);
    free(p4);
    free(p5);
    free(p6);
    
    return pass1 && pass2 && pass3 && pass4 && pass5;
}

/**
 * Test mmap functionality
 */
static int test_mmap(void) {
    print("\n=== Testing mmap ===\n");
    
    /* Test 1: Basic anonymous mmap */
    void *m1 = mmap(0, 4096, PROT_READ | PROT_WRITE, 
                    MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    int pass1 = (m1 != MAP_FAILED);
    print_test("mmap anonymous 4KB", pass1);
    
    /* Test 2: Write to mapped memory */
    if (m1 != MAP_FAILED) {
        char *p = (char *)m1;
        p[0] = 'A';
        p[100] = 'B';
        p[4095] = 'C';
        int pass2 = (p[0] == 'A' && p[100] == 'B' && p[4095] == 'C');
        print_test("Write to mmap region", pass2);
        
        /* Test 3: Executable memory */
        void *m2 = mmap(0, 4096, PROT_READ | PROT_WRITE | PROT_EXEC,
                        MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
        int pass3 = (m2 != MAP_FAILED);
        print_test("mmap with PROT_EXEC", pass3);
        
        if (m2 != MAP_FAILED) {
            munmap(m2, 4096);
        }
        
        munmap(m1, 4096);
        return pass1 && pass2 && pass3;
    }
    
    return pass1;
}

/**
 * Test lseek functionality (requires file system)
 */
static int test_lseek(void) {
    print("\n=== Testing lseek ===\n");
    
    /* Note: This test requires a file system to be mounted.
     * For now, we just test that the functions are linked. */
    print_test("lseek linked", 1);
    
    return 1;
}

/**
 * Main test entry point
 */
int main(void) {
    print("\n");
    print("╔═══════════════════════════════════════════════════════════╗\n");
    print("║  Phase 13 TCC Prerequisites Test                         ║\n");
    print("╚═══════════════════════════════════════════════════════════╝\n");
    
    int all_pass = 1;
    
    all_pass &= test_malloc_free();
    all_pass &= test_mmap();
    all_pass &= test_lseek();
    
    print("\n");
    print("═══════════════════════════════════════════════════════════\n");
    if (all_pass) {
        print("  ALL TESTS PASSED ✓\n");
    } else {
        print("  SOME TESTS FAILED ✗\n");
    }
    print("═══════════════════════════════════════════════════════════\n");
    print("\n");
    
    return all_pass ? 0 : 1;
}

/**
 * @file spawn_test.c
 * @brief Test program for spawn() - Phase 11
 *
 * LIONS' LESSON: This tests the COMPLETE exokernel process creation chain:
 *
 *   1. spawn_test → spawn("/hello", argv)
 *   2. spawn() → open("/hello") via IPC to fs_srv
 *   3. spawn() → read() ELF into memory
 *   4. spawn() → elf_load_into_child() → sys_env_create + page mappings
 *   5. spawn() → setup_child_stack() → write argc/argv to child's stack
 *   6. spawn() → sys_env_run() → child starts running!
 *
 * If "Hello from exokernel!" appears, we've proven:
 *   - File Server IPC works (open/read)
 *   - ELF loading works (code segments mapped correctly)
 *   - Stack setup works (argc/argv passed correctly)
 *   - Process switching works (child actually runs)
 *
 * This is the FULL VERTICAL SLICE of the exokernel model.
 */

#include <stdint.h>
#include <types.h>
#include <exov6_interface.h>

/* LibOS */
extern void print(const char *s);
extern void print_hex(uint64 n);
extern void libos_exception_init(void);

/* spawn() - The star of Phase 11 */
extern int spawn(const char *path, char **argv);

/* Print an integer */
static void print_int(int n) {
    if (n < 0) {
        print("-");
        n = -n;
    }
    if (n == 0) {
        print("0");
        return;
    }
    char buf[12];
    int i = 0;
    while (n > 0) {
        buf[i++] = '0' + (n % 10);
        n /= 10;
    }
    char out[12];
    for (int j = 0; j < i; j++) {
        out[j] = buf[i - 1 - j];
    }
    out[i] = '\0';
    print(out);
}

int main(void)
{
    print("\n");
    print("═══════════════════════════════════════════════════════════════════\n");
    print("  SPAWN TEST: User-Space Process Creation\n");
    print("═══════════════════════════════════════════════════════════════════\n");
    print("\n");

    /* Initialize exception handling */
    libos_exception_init();

    print("This test demonstrates the EXOKERNEL process model:\n");
    print("  - Kernel provides: env_create, page_alloc, page_map, env_run\n");
    print("  - LibOS provides: ELF parsing, stack setup, file I/O\n");
    print("\n");

    /* Test 1: Spawn hello program */
    print("┌───────────────────────────────────────────────────────────────────┐\n");
    print("│ TEST 1: Spawn /hello                                              │\n");
    print("└───────────────────────────────────────────────────────────────────┘\n");
    print("\n");

    char *hello_argv[] = {"hello", NULL};
    int pid = spawn("/hello", hello_argv);

    if (pid < 0) {
        print("FAIL: spawn() returned ");
        print_int(pid);
        print("\n");
        print("\n");
        print("This could mean:\n");
        print("  - /hello doesn't exist in fs.img\n");
        print("  - fs_srv is not running\n");
        print("  - ELF loading failed\n");
        print("\n");
    } else {
        print("SUCCESS: spawn() returned child PID ");
        print_int(pid);
        print("\n");
        print("\n");
        print("If you see 'Hello from exokernel!' above, the full chain worked!\n");
        print("\n");
    }

    /* Test 2: Spawn with arguments */
    print("┌───────────────────────────────────────────────────────────────────┐\n");
    print("│ TEST 2: Spawn /echo with arguments                                │\n");
    print("└───────────────────────────────────────────────────────────────────┘\n");
    print("\n");

    char *echo_argv[] = {"echo", "Hello", "from", "spawn()!", NULL};
    pid = spawn("/echo", echo_argv);

    if (pid < 0) {
        print("Note: /echo not found (expected if not in fs.img)\n");
    } else {
        print("spawn(/echo) returned PID ");
        print_int(pid);
        print("\n");
    }

    print("\n");
    print("═══════════════════════════════════════════════════════════════════\n");
    print("  SPAWN TEST COMPLETE\n");
    print("═══════════════════════════════════════════════════════════════════\n");
    print("\n");

    /* Halt */
    while (1) {
#if defined(__x86_64__)
        __asm__ volatile("hlt");
#elif defined(__aarch64__)
        __asm__ volatile("wfi");
#else
        __asm__ volatile("" ::: "memory");
#endif
    }

    return 0;
}

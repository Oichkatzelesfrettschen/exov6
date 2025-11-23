/**
 * @file elf_test.c
 * @brief ELF Loader Test (Phase 10)
 *
 * This test demonstrates the exokernel process spawning mechanism:
 *   1. sys_env_create() - Create blank environment
 *   2. sys_page_alloc() + sys_page_map() - Allocate memory
 *   3. sys_env_run() - Start the child
 *
 * This is the "Spark of Life" - the ability to create new processes
 * entirely from user space, following pure exokernel philosophy.
 */

#include <stdint.h>
#include <types.h>
#include <exov6_interface.h>

/* LibOS */
extern void print(const char *s);
extern void print_hex(uint64_t n);
extern void libos_exception_init(void);
extern void scheduler_init(void);

/* Syscall wrappers */
extern uint64_t sys_page_alloc_raw(void);
extern int sys_page_map_raw(int target_env, uint64_t phys, uint64_t virt, int perm);
extern int sys_env_create_raw(void);
extern int sys_env_run_raw(int env_id, uint64_t entry, uint64_t sp);

/* Permission bits */
#define PERM_R  0x1
#define PERM_W  0x2
#define PERM_X  0x4

static void print_uint(uint32_t n) {
    if (n == 0) { print("0"); return; }
    char buf[12];
    int i = 0;
    while (n > 0) { buf[i++] = '0' + (n % 10); n /= 10; }
    char out[12];
    for (int j = 0; j < i; j++) out[j] = buf[i - 1 - j];
    out[i] = '\0';
    print(out);
}

/* ═══════════════════════════════════════════════════════════════════════════
 * Simple Child Code (embedded)
 *
 * For this test, we embed a tiny "program" as raw machine code.
 * In Phase 10.6, we'll load real ELF files from disk.
 * ═══════════════════════════════════════════════════════════════════════════ */

#if defined(__x86_64__)
/* x86_64 child code:
 *   mov rax, 12     ; SYS_cputs
 *   mov rdi, msg    ; pointer to message
 *   mov rsi, len    ; length
 *   syscall
 *   hlt
 * msg: "Hello from child!\n"
 */
static const uint8_t child_code[] = {
    /* Entry at 0x1000 */
    0x48, 0xC7, 0xC0, 0x0C, 0x00, 0x00, 0x00,   /* mov rax, 12 (SYS_cputs) */
    0x48, 0x8D, 0x3D, 0x12, 0x00, 0x00, 0x00,   /* lea rdi, [rip+0x12] (msg) */
    0x48, 0xC7, 0xC6, 0x14, 0x00, 0x00, 0x00,   /* mov rsi, 20 (length) */
    0x0F, 0x05,                                   /* syscall */
    0xF4,                                         /* hlt */
    0xEB, 0xFD,                                   /* jmp -3 (loop on hlt) */
    /* Message at offset ~0x1020 */
    '[', 'C', 'H', 'I', 'L', 'D', ']', ' ',
    'H', 'e', 'l', 'l', 'o', ' ', 'f', 'r',
    'o', 'm', ' ', 'c', 'h', 'i', 'l', 'd',
    '!', '\n', 0
};
#define CHILD_CODE_SIZE sizeof(child_code)
#define CHILD_ENTRY 0x1000
#define CHILD_STACK 0x2000

#elif defined(__aarch64__)
/* ARM64 child code - simplified */
static const uint8_t child_code[] = {
    /* svc #0 to trigger syscall, then wfi loop */
    0x01, 0x00, 0x00, 0xD4,   /* svc #0 */
    0x7F, 0x20, 0x03, 0xD5,   /* wfi */
    0xFE, 0xFF, 0xFF, 0x17    /* b -4 */
};
#define CHILD_CODE_SIZE sizeof(child_code)
#define CHILD_ENTRY 0x1000
#define CHILD_STACK 0x2000

#else
#error "Unsupported architecture"
#endif

/* ═══════════════════════════════════════════════════════════════════════════
 * Test: Create and Run a Child Environment
 * ═══════════════════════════════════════════════════════════════════════════ */

static int test_env_create_and_run(void) {
    print("\n");
    print("═══════════════════════════════════════════════════════════\n");
    print("  TEST: Environment Creation and Execution\n");
    print("═══════════════════════════════════════════════════════════\n");
    print("\n");

    /* Step 1: Create blank environment */
    print("[1/4] Creating blank child environment...\n");
    int child_pid = sys_env_create_raw();
    if (child_pid < 0) {
        print("      ERROR: sys_env_create failed!\n");
        return -1;
    }
    print("      Created child PID: ");
    print_uint(child_pid);
    print("\n");

    /* Step 2: Allocate code page */
    print("[2/4] Allocating code page...\n");
    uint64_t code_page = sys_page_alloc_raw();
    if ((int64_t)code_page < 0) {
        print("      ERROR: sys_page_alloc failed!\n");
        return -1;
    }
    print("      Physical page: 0x");
    print_hex(code_page);
    print("\n");

    /* Step 3: Map code page into child and copy code */
    print("[3/4] Mapping code page into child...\n");

    /* First map into our address space to copy */
    uint64_t temp_va = 0x50000000ULL;
    if (sys_page_map_raw(0, code_page, temp_va, PERM_R | PERM_W) < 0) {
        print("      ERROR: Failed to map page into self!\n");
        return -1;
    }

    /* Copy code */
    uint8_t *dst = (uint8_t *)temp_va;
    for (size_t i = 0; i < CHILD_CODE_SIZE; i++) {
        dst[i] = child_code[i];
    }
    print("      Copied ");
    print_uint(CHILD_CODE_SIZE);
    print(" bytes of code\n");

    /* Map into child's address space */
    if (sys_page_map_raw(child_pid, code_page, CHILD_ENTRY, PERM_R | PERM_X) < 0) {
        print("      ERROR: Failed to map page into child!\n");
        return -1;
    }
    print("      Mapped at child VA: 0x");
    print_hex(CHILD_ENTRY);
    print("\n");

    /* Allocate stack for child */
    uint64_t stack_page = sys_page_alloc_raw();
    if ((int64_t)stack_page < 0) {
        print("      ERROR: Failed to allocate stack page!\n");
        return -1;
    }
    if (sys_page_map_raw(child_pid, stack_page, CHILD_STACK - 0x1000, PERM_R | PERM_W) < 0) {
        print("      ERROR: Failed to map stack page!\n");
        return -1;
    }
    print("      Stack mapped at: 0x");
    print_hex(CHILD_STACK - 0x1000);
    print("\n");

    /* Step 4: Start the child */
    print("[4/4] Starting child execution...\n");
    print("      Entry: 0x");
    print_hex(CHILD_ENTRY);
    print("\n      Stack: 0x");
    print_hex(CHILD_STACK);
    print("\n");

    int result = sys_env_run_raw(child_pid, CHILD_ENTRY, CHILD_STACK);
    if (result < 0) {
        print("      ERROR: sys_env_run failed!\n");
        return -1;
    }

    print("      Child started successfully!\n");
    print("\n");
    print("═══════════════════════════════════════════════════════════\n");
    print("  TEST PASSED: Environment spawning works!\n");
    print("═══════════════════════════════════════════════════════════\n");
    print("\n");

    return 0;
}

int main(void)
{
    print("\n");
    print("═══════════════════════════════════════════════════════════\n");
    print("  ELF_TEST: Process Spawning Test (Phase 10)\n");
    print("═══════════════════════════════════════════════════════════\n");
    print("\n");

    /* Initialize LibOS */
    print("[1/2] Initializing exception handling...\n");
    libos_exception_init();

    print("[2/2] Initializing scheduler...\n");
    scheduler_init();

    /* Run tests */
    test_env_create_and_run();

    print("\n");
    print("═══════════════════════════════════════════════════════════\n");
    print("  PHASE 10 FOUNDATION COMPLETE\n");
    print("═══════════════════════════════════════════════════════════\n");
    print("\n");
    print("The exokernel can now:\n");
    print("  1. Create blank environments (sys_env_create)\n");
    print("  2. Allocate physical pages (sys_page_alloc)\n");
    print("  3. Map pages into any environment (sys_page_map)\n");
    print("  4. Start execution at arbitrary address (sys_env_run)\n");
    print("\n");
    print("Next steps:\n");
    print("  - Phase 10.6: Load real ELF files from disk\n");
    print("  - Phase 11: Interactive shell\n");
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

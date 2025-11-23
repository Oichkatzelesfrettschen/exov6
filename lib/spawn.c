/**
 * @file spawn.c
 * @brief User-Space Process Spawning (Phase 11 - "The Spark of Life")
 *
 * ╔═══════════════════════════════════════════════════════════════════════════╗
 * ║  LIONS' COMMENTARY FOR THE POST-MONOLITHIC AGE                            ║
 * ║                                                                           ║
 * ║  LESSON: Why spawn() instead of fork()+exec()?                            ║
 * ║                                                                           ║
 * ║  In UNIX V6:                                                              ║
 * ║    fork() - Kernel clones parent's entire address space                   ║
 * ║    exec() - Kernel replaces address space with new program                ║
 * ║                                                                           ║
 * ║  This is WASTEFUL. fork() copies all memory, exec() throws it away.      ║
 * ║  Modern UNIX has copy-on-write, but the semantic overhead remains.        ║
 * ║                                                                           ║
 * ║  In the EXOKERNEL model:                                                  ║
 * ║    spawn() - Parent creates child from scratch, loads ELF, starts it      ║
 * ║                                                                           ║
 * ║  "We implemented spawn rather than a UNIX-style exec because spawn is     ║
 * ║   easier to implement from user space in 'exokernel fashion', without     ║
 * ║   special help from the kernel." - MIT 6.828 Lab 5                        ║
 * ║                                                                           ║
 * ║  The kernel provides only:                                                ║
 * ║    - sys_env_create() → Create blank environment                          ║
 * ║    - sys_page_alloc() → Allocate physical page                            ║
 * ║    - sys_page_map()   → Map page into address space                       ║
 * ║    - sys_env_run()    → Start execution                                   ║
 * ║                                                                           ║
 * ║  ALL ELF parsing, memory layout, stack setup is done HERE in user space.  ║
 * ╚═══════════════════════════════════════════════════════════════════════════╝
 *
 * Architecture:
 *
 *   spawn("/bin/cat", ["cat", "file"])
 *          │
 *          ├──► [1] open("/bin/cat") via IPC to fs_srv
 *          │
 *          ├──► [2] read() entire ELF into memory buffer
 *          │
 *          ├──► [3] elf_load_into_child()
 *          │        └── sys_env_create() → blank child
 *          │        └── allocate + map code/data pages
 *          │        └── copy ELF segments
 *          │        └── allocate stack
 *          │
 *          ├──► [4] setup_child_stack()
 *          │        └── map child's stack into our space temporarily
 *          │        └── push argv strings
 *          │        └── push argv[] pointer array
 *          │        └── push argc
 *          │
 *          └──► [5] sys_env_run(child, entry, sp)
 *                   └── child starts running!
 */

#include <stdint.h>
#include <types.h>
#include <exov6_interface.h>
#include "elf/elf_loader.h"

/* ═══════════════════════════════════════════════════════════════════════════
 * External Dependencies
 * ═══════════════════════════════════════════════════════════════════════════ */

/* File system client (lib/fs_client.c) */
extern int open(const char *path, int flags);
extern int read(int fd, void *buf, int n);
extern int close(int fd);

/* ELF loader functions declared in elf/elf_loader.h */

/* Syscall wrappers (lib/syscall.c) */
extern uint64_t sys_page_alloc_raw(void);
extern int sys_page_map_raw(int target_env, uint64_t phys, uint64_t virt, int perm);
extern int sys_env_run_raw(int env_id, uint64_t entry, uint64_t sp);

/* Debug output */
extern void print(const char *s);
extern void print_hex(uint64_t n);

/* Permission bits */
#define PERM_R  0x1
#define PERM_W  0x2

/* Open flags (minimal) */
#define O_RDONLY  0

/* ═══════════════════════════════════════════════════════════════════════════
 * Configuration
 * ═══════════════════════════════════════════════════════════════════════════ */

/* Buffer for reading ELF files (16KB should be enough for small programs) */
#define SPAWN_ELF_BUFFER_SIZE   (16 * 4096)

/* Where child's stack lives (from elf_loader.h) */
#define CHILD_STACK_TOP         0x7FFFFFFFF000ULL

/* Page size */
#define PAGE_SIZE               4096

/* Maximum arguments */
#define MAX_ARGC                32
#define MAX_ARG_LEN             128

/* Temporary VA for mapping child's stack pages into our space */
#define TEMP_STACK_VA           0x6800000000ULL

/* ═══════════════════════════════════════════════════════════════════════════
 * String Helpers (freestanding - no libc)
 * ═══════════════════════════════════════════════════════════════════════════ */

static int strlen_spawn(const char *s) {
    int len = 0;
    while (*s++) len++;
    return len;
}

static void strcpy_spawn(char *dst, const char *src) {
    while (*src) *dst++ = *src++;
    *dst = '\0';
}

/* ═══════════════════════════════════════════════════════════════════════════
 * ELF Buffer
 *
 * LESSON: We read the entire ELF into memory before loading.
 * This is simpler than demand-loading (which would require page fault handling).
 * Real systems (Linux, BSD) use demand paging for efficiency.
 * ═══════════════════════════════════════════════════════════════════════════ */

static uint8_t elf_buffer[SPAWN_ELF_BUFFER_SIZE] __attribute__((aligned(4096)));

/* ═══════════════════════════════════════════════════════════════════════════
 * setup_child_stack - The Bootstrap Handshake
 *
 * LIONS' LESSON: This is where parent and child meet.
 *
 * The x86_64/AArch64 ABI specifies how main() receives its arguments:
 *
 *   Stack layout (growing down):
 *   ┌─────────────────────────┐ High addresses
 *   │  "arg2\0"               │  ← argv strings
 *   │  "arg1\0"               │
 *   │  "prog\0"               │
 *   ├─────────────────────────┤
 *   │  NULL                   │  ← argv[argc] = NULL
 *   │  ptr to "arg2"          │  ← argv[2]
 *   │  ptr to "arg1"          │  ← argv[1]
 *   │  ptr to "prog"          │  ← argv[0]
 *   ├─────────────────────────┤
 *   │  argc                   │  ← bottom of stack
 *   └─────────────────────────┘ Low addresses (SP points here)
 *
 * The CHALLENGE: child's stack is in CHILD's address space.
 * We must map it into OUR space to write to it.
 *
 * @param child_pid   Child's PID
 * @param argv        NULL-terminated argument array
 * @param stack_phys  Physical address of top stack page
 * @return            Stack pointer to use when starting child
 * ═══════════════════════════════════════════════════════════════════════════ */

static uint64_t setup_child_stack(int child_pid, char **argv)
{
    (void)child_pid;  /* We use TEMP_STACK_VA which was already mapped */

    /*
     * The stack was allocated by elf_load_into_child() at CHILD_STACK_TOP.
     * We need to map the TOP page of child's stack into our space to write.
     *
     * Stack grows DOWN, so:
     *   - CHILD_STACK_TOP is the highest address
     *   - Top page is at (CHILD_STACK_TOP - PAGE_SIZE) to CHILD_STACK_TOP
     *   - We write at the TOP of this page, then SP points below our data
     */

    /* Count arguments */
    int argc = 0;
    while (argv[argc] && argc < MAX_ARGC) {
        argc++;
    }

    print("[SPAWN] Setting up stack with ");
    print_hex(argc);
    print(" arguments\n");

    /*
     * We need to map the child's stack page into our address space.
     * The stack page is at (CHILD_STACK_TOP - PAGE_SIZE) in child's space.
     *
     * TRICKY: We already mapped it via elf_load_into_child, but we don't
     * have direct access. We need to re-map from the same physical page.
     *
     * For now, use a simpler approach: assume stack is empty and fresh,
     * compute where we'd write from the TOP of the temp mapping.
     *
     * The child's stack top page is already mapped. We need its PA.
     * SIMPLIFICATION: Allocate a FRESH page for the top of stack and
     * map it to both child and us. This is wasteful but simple.
     */

    uint64_t stack_page_pa = sys_page_alloc_raw();
    if ((int64_t)stack_page_pa < 0) {
        print("[SPAWN] ERROR: Cannot allocate stack setup page\n");
        return 0;
    }

    /* Map to child's stack top page */
    uint64_t child_stack_va = CHILD_STACK_TOP - PAGE_SIZE;
    if (sys_page_map_raw(child_pid, stack_page_pa, child_stack_va, PERM_R | PERM_W) < 0) {
        print("[SPAWN] ERROR: Cannot map stack to child\n");
        return 0;
    }

    /* Map to our temp area */
    if (sys_page_map_raw(0, stack_page_pa, TEMP_STACK_VA, PERM_R | PERM_W) < 0) {
        print("[SPAWN] ERROR: Cannot map stack to self\n");
        return 0;
    }

    /*
     * Now we can write to TEMP_STACK_VA and it affects child's stack.
     * The page is 4KB, we work from the TOP down.
     */

    char *page_base = (char *)TEMP_STACK_VA;
    char *page_top = page_base + PAGE_SIZE;

    /* Start writing strings from the top of the page */
    char *string_ptr = page_top;
    uint64_t argv_ptrs[MAX_ARGC + 1];

    /* Copy argument strings (from top down) */
    for (int i = argc - 1; i >= 0; i--) {
        int len = strlen_spawn(argv[i]) + 1;  /* Include null terminator */
        string_ptr -= len;
        strcpy_spawn(string_ptr, argv[i]);

        /* Calculate what this address will be in CHILD's address space */
        uint64_t offset = string_ptr - page_base;
        argv_ptrs[i] = child_stack_va + offset;

        print("[SPAWN]   argv[");
        print_hex(i);
        print("] = \"");
        print(argv[i]);
        print("\" at 0x");
        print_hex(argv_ptrs[i]);
        print("\n");
    }
    argv_ptrs[argc] = 0;  /* NULL terminator for argv */

    /* Align string_ptr down to 8-byte boundary */
    string_ptr = (char *)((uint64_t)string_ptr & ~7ULL);

    /* Now write argv[] array below the strings */
    uint64_t *argv_array = (uint64_t *)string_ptr;
    argv_array -= (argc + 1);  /* Make room for argv[0..argc] including NULL */

    for (int i = 0; i <= argc; i++) {
        argv_array[i] = argv_ptrs[i];
    }

    /* Calculate argv pointer in child's address space */
    uint64_t child_argv = child_stack_va + ((char *)argv_array - page_base);

    /* Write argc below argv */
    uint64_t *argc_ptr = argv_array - 1;
    *argc_ptr = (uint64_t)argc;

    /* Calculate final stack pointer in child's address space */
    uint64_t child_sp = child_stack_va + ((char *)argc_ptr - page_base);

    /* Align SP to 16 bytes (x86_64/AArch64 ABI requirement) */
    child_sp &= ~15ULL;

    print("[SPAWN] Child stack: argc=");
    print_hex(argc);
    print(" argv=0x");
    print_hex(child_argv);
    print(" sp=0x");
    print_hex(child_sp);
    print("\n");

    /* TODO: Unmap TEMP_STACK_VA from our space */

    return child_sp;
}

/* ═══════════════════════════════════════════════════════════════════════════
 * spawn() - Create a New Process from an ELF File
 *
 * LIONS' LESSON: This is the EXOKERNEL way of creating processes.
 *
 * In UNIX: fork() + exec() requires kernel to understand address spaces deeply.
 * In ExoV6: spawn() does everything in user space with raw primitives.
 *
 * The kernel is IGNORANT of:
 *   - What an ELF file is
 *   - What "arguments" mean
 *   - What a "process" really is (it just knows "environments")
 *
 * We, the LibOS, define ALL of this.
 *
 * @param path   Path to ELF executable (via fs_srv)
 * @param argv   NULL-terminated argument array
 * @return       Child's PID on success, negative on error
 * ═══════════════════════════════════════════════════════════════════════════ */

int spawn(const char *path, char **argv)
{
    print("\n");
    print("═══════════════════════════════════════════════════════════════════\n");
    print("  SPAWN: Creating new process from ELF\n");
    print("═══════════════════════════════════════════════════════════════════\n");
    print("  Path: ");
    print(path);
    print("\n");

    /* ─────────────────────────────────────────────────────────────────────
     * Step 1: Open ELF file via File Server IPC
     *
     * LESSON: We don't call the kernel to open files.
     * We send an IPC message to fs_srv, which owns the disk.
     * ───────────────────────────────────────────────────────────────────── */

    print("[SPAWN] Step 1: Opening ELF file via fs_srv...\n");

    int fd = open(path, O_RDONLY);
    if (fd < 0) {
        print("[SPAWN] ERROR: Failed to open '");
        print(path);
        print("'\n");
        return -1;
    }

    print("[SPAWN] Opened as fd ");
    print_hex(fd);
    print("\n");

    /* ─────────────────────────────────────────────────────────────────────
     * Step 2: Read entire ELF into memory
     *
     * LESSON: We read the whole file. A production system would:
     *   - Just read headers first
     *   - Demand-page the rest on page faults
     * But that requires page fault handling infrastructure.
     * ───────────────────────────────────────────────────────────────────── */

    print("[SPAWN] Step 2: Reading ELF into buffer...\n");

    uint64_t elf_size = 0;
    int n;

    while ((n = read(fd, elf_buffer + elf_size, 4096)) > 0) {
        elf_size += n;
        if (elf_size >= SPAWN_ELF_BUFFER_SIZE) {
            print("[SPAWN] ERROR: ELF too large\n");
            close(fd);
            return -1;
        }
    }

    close(fd);

    print("[SPAWN] Read ");
    print_hex(elf_size);
    print(" bytes\n");

    /* ─────────────────────────────────────────────────────────────────────
     * Step 3: Load ELF into child environment
     *
     * LESSON: elf_load_into_child() does:
     *   - sys_env_create() → blank child
     *   - Parse ELF headers (LibOS work!)
     *   - Allocate pages for code/data
     *   - Map pages into child's address space
     *   - Copy segment data
     *   - Allocate stack
     *
     * The kernel just provides raw page operations.
     * ───────────────────────────────────────────────────────────────────── */

    print("[SPAWN] Step 3: Loading ELF into child...\n");

    struct elf_load_result result;
    int child_pid = elf_load_into_child(elf_buffer, elf_size, &result);

    if (child_pid < 0) {
        print("[SPAWN] ERROR: ELF loading failed\n");
        return child_pid;
    }

    print("[SPAWN] Child PID ");
    print_hex(child_pid);
    print(" created, entry=0x");
    print_hex(result.entry_point);
    print("\n");

    /* ─────────────────────────────────────────────────────────────────────
     * Step 4: Set up child's stack with arguments
     *
     * LESSON: The ABI (Application Binary Interface) defines how main()
     * receives argc and argv. We construct this on the stack.
     *
     * This is PURE USER SPACE work. The kernel has no idea what "arguments"
     * are. It doesn't know C calling conventions. We do.
     * ───────────────────────────────────────────────────────────────────── */

    print("[SPAWN] Step 4: Setting up child stack...\n");

    uint64_t child_sp = setup_child_stack(child_pid, argv);
    if (child_sp == 0) {
        print("[SPAWN] ERROR: Stack setup failed\n");
        /* TODO: Destroy child environment */
        return -1;
    }

    /* ─────────────────────────────────────────────────────────────────────
     * Step 5: Start the child!
     *
     * LESSON: sys_env_run() is the kernel primitive that starts execution.
     * It sets the child's instruction pointer to entry_point,
     * stack pointer to child_sp, and makes it RUNNABLE.
     *
     * From the child's perspective, it "wakes up" at entry_point with
     * a pre-configured stack. It has no idea how it got there.
     * ───────────────────────────────────────────────────────────────────── */

    print("[SPAWN] Step 5: Starting child at entry=0x");
    print_hex(result.entry_point);
    print(" sp=0x");
    print_hex(child_sp);
    print("\n");

    int err = sys_env_run_raw(child_pid, result.entry_point, child_sp);
    if (err < 0) {
        print("[SPAWN] ERROR: sys_env_run failed\n");
        return err;
    }

    print("═══════════════════════════════════════════════════════════════════\n");
    print("  SPAWN COMPLETE: Child PID ");
    print_hex(child_pid);
    print(" is now running!\n");
    print("═══════════════════════════════════════════════════════════════════\n");
    print("\n");

    return child_pid;
}

/* ═══════════════════════════════════════════════════════════════════════════
 * spawnl() - Convenience wrapper with inline arguments
 *
 * spawn() requires a pre-built argv array.
 * spawnl() takes arguments inline like execl().
 *
 * Example: spawnl("/bin/echo", "echo", "hello", "world", NULL);
 * ═══════════════════════════════════════════════════════════════════════════ */

int spawnl(const char *path, const char *arg0, ...)
{
    /* Simple implementation: just handle up to 8 args */
    const char *args[9];
    args[0] = arg0;

    /* TODO: Use va_list to properly iterate varargs */
    /* For now, this is a stub - use spawn() directly */
    args[1] = 0;

    return spawn(path, (char **)args);
}

/* ═══════════════════════════════════════════════════════════════════════════
 * PEDAGOGICAL SUMMARY
 *
 * What we've built here is a COMPLETE USER-SPACE PROCESS LOADER.
 *
 * Compare to UNIX V6:
 *   - fork(): Kernel clones address space (savu/retu in assembly)
 *   - exec(): Kernel parses ELF/a.out, replaces address space
 *   - wait(): Kernel tracks parent-child relationships
 *
 * In ExoV6:
 *   - spawn(): LibOS reads ELF via IPC, calls raw kernel primitives
 *   - The kernel is a HARDWARE MULTIPLEXER, nothing more
 *   - All "process" semantics live HERE
 *
 * BENEFITS:
 * 1. Kernel is smaller (fewer bugs, easier to verify)
 * 2. Different LibOS can implement different process models
 * 3. Everything is explicit (no hidden kernel state)
 *
 * COSTS:
 * 1. More code in user space
 * 2. IPC overhead for file operations
 * 3. More complex spawn() than fork()+exec()
 *
 * The EXOKERNEL BET: Flexibility and isolation are worth the complexity.
 * The kernel provides MECHANISM. We provide POLICY.
 *
 * "The trick is to separate mechanism from policy wherever possible."
 *   - Per Brinch Hansen, 1970
 * ═══════════════════════════════════════════════════════════════════════════ */

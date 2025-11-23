/**
 * @file sh.c
 * @brief ExoV6 Shell - "The Voice" (Phase 11)
 *
 * ╔═══════════════════════════════════════════════════════════════════════════╗
 * ║  LIONS' COMMENTARY FOR THE POST-MONOLITHIC AGE                            ║
 * ║                                                                           ║
 * ║  LESSON: The shell is just another user program.                          ║
 * ║                                                                           ║
 * ║  In UNIX V6, the shell is special only because it's process 1's child.    ║
 * ║  Here, the shell demonstrates the FULL exokernel architecture:            ║
 * ║                                                                           ║
 * ║    Shell ─── spawn() ───► Child Process                                   ║
 * ║      │                         │                                          ║
 * ║      └── IPC to fs_srv ────────┘                                          ║
 * ║                │                                                          ║
 * ║           elf_load_into_child()                                           ║
 * ║                │                                                          ║
 * ║           sys_env_run()                                                   ║
 * ║                                                                          ║
 * ║  The kernel never "executes" programs. It just switches contexts.         ║
 * ╚═══════════════════════════════════════════════════════════════════════════╝
 *
 * EVOLUTION from UNIX V6:
 *   V6: fork() + exec() - Kernel clones address space, then replaces it
 *   ExoV6: spawn()      - LibOS builds new process from scratch
 *
 * Current limitations (Phase 11.4):
 *   - No console input yet (runs demo sequence)
 *   - No wait() - shell doesn't wait for children
 *   - No pipes or redirection
 *
 * These will be added in subsequent phases.
 */

#include <stdint.h>
#include <types.h>
#include <exov6_interface.h>

/* ═══════════════════════════════════════════════════════════════════════════
 * External Dependencies
 * ═══════════════════════════════════════════════════════════════════════════ */

/* LibOS */
extern void print(const char *s);
extern void print_hex(uint64 n);
extern void libos_exception_init(void);

/* spawn() - The star of Phase 11 */
extern int spawn(const char *path, char **argv);

/* ═══════════════════════════════════════════════════════════════════════════
 * Configuration
 * ═══════════════════════════════════════════════════════════════════════════ */

#define MAXARGS 10
#define MAXLINE 100

/* ═══════════════════════════════════════════════════════════════════════════
 * Helpers
 * ═══════════════════════════════════════════════════════════════════════════ */

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

/* Simple string comparison */
static int strcmp_sh(const char *a, const char *b) {
    while (*a && *b && *a == *b) {
        a++;
        b++;
    }
    return *a - *b;
}

/* Simple string length */
static int strlen_sh(const char *s) {
    int len = 0;
    while (*s++) len++;
    return len;
}

/* ═══════════════════════════════════════════════════════════════════════════
 * Built-in Commands
 *
 * LESSON: Some commands must be built-in because they affect the shell itself.
 * In UNIX V6, 'cd' changes the shell's current directory - can't be external.
 * ═══════════════════════════════════════════════════════════════════════════ */

static void cmd_help(void) {
    print("\n");
    print("ExoV6 Shell Commands:\n");
    print("  help      - Show this help\n");
    print("  hello     - Run /hello program\n");
    print("  about     - About ExoV6\n");
    print("  demo      - Run demo sequence\n");
    print("\n");
    print("Architecture note:\n");
    print("  This shell uses spawn() instead of fork()+exec().\n");
    print("  The kernel provides only raw primitives; LibOS handles policy.\n");
    print("\n");
}

static void cmd_about(void) {
    print("\n");
    print("═══════════════════════════════════════════════════════════════════\n");
    print("  ExoV6 - The Pedagogical Exokernel\n");
    print("═══════════════════════════════════════════════════════════════════\n");
    print("\n");
    print("  'Lions' Commentary for the Post-Monolithic Age'\n");
    print("\n");
    print("  An exokernel provides only the minimal primitives to securely\n");
    print("  export hardware:\n");
    print("\n");
    print("    KERNEL (Mechanism):  pages, address spaces, CPU time, IPC\n");
    print("    LIBOS  (Policy):     files, processes, sockets, memory layout\n");
    print("\n");
    print("  Inspired by:\n");
    print("    - MIT Exokernel (Xok/ExOS)\n");
    print("    - seL4 Microkernel\n");
    print("    - xv6 Teaching OS\n");
    print("    - Lions' Commentary on UNIX V6\n");
    print("\n");
}

/* ═══════════════════════════════════════════════════════════════════════════
 * Command Execution via spawn()
 *
 * LIONS' LESSON: This is the key difference from UNIX V6.
 *
 * UNIX V6 shell:
 *   pid = fork();     // Kernel clones entire address space
 *   if (pid == 0)
 *     exec(argv[0]);  // Kernel replaces address space
 *   wait();           // Kernel tracks parent-child
 *
 * ExoV6 shell:
 *   spawn(argv[0]);   // LibOS builds new process from scratch
 *   // Kernel just provides: env_create, page_map, env_run
 *
 * Benefits:
 *   - No COW overhead from fork
 *   - Cleaner semantics (no zombie processes)
 *   - Kernel is simpler (no exec syscall)
 * ═══════════════════════════════════════════════════════════════════════════ */

static void run_command(const char *cmd) {
    print("$ ");
    print(cmd);
    print("\n");

    if (strcmp_sh(cmd, "help") == 0) {
        cmd_help();
    }
    else if (strcmp_sh(cmd, "about") == 0) {
        cmd_about();
    }
    else if (strcmp_sh(cmd, "hello") == 0) {
        char *argv[] = {"hello", NULL};
        int pid = spawn("/hello", argv);
        if (pid < 0) {
            print("sh: spawn failed for /hello\n");
            print("    (Is fs_srv running? Is /hello in fs.img?)\n");
        } else {
            print("sh: spawned /hello with PID ");
            print_int(pid);
            print("\n");
            /* TODO: wait(pid) when wait syscall is implemented */
        }
    }
    else if (strcmp_sh(cmd, "demo") == 0) {
        /* Run demo sequence */
        cmd_help();
        cmd_about();
    }
    else {
        print("sh: unknown command: ");
        print(cmd);
        print("\n");
        print("    Type 'help' for available commands\n");
    }
}

/* ═══════════════════════════════════════════════════════════════════════════
 * Demo Mode
 *
 * Until we have console input (getchar syscall), run predefined sequence.
 * ═══════════════════════════════════════════════════════════════════════════ */

static void run_demo(void) {
    print("\n");
    print("┌───────────────────────────────────────────────────────────────────┐\n");
    print("│  DEMO MODE: Console input not yet implemented                     │\n");
    print("│  Running predefined command sequence                              │\n");
    print("└───────────────────────────────────────────────────────────────────┘\n");
    print("\n");

    run_command("help");
    run_command("about");

    print("\n");
    print("Attempting to spawn /hello...\n");
    print("(Requires fs_srv running and /hello in file system)\n");
    print("\n");
    run_command("hello");
}

/* ═══════════════════════════════════════════════════════════════════════════
 * Main Entry Point
 * ═══════════════════════════════════════════════════════════════════════════ */

int main(void)
{
    print("\n");
    print("═══════════════════════════════════════════════════════════════════\n");
    print("  ███████╗██╗  ██╗ ██████╗ ██╗   ██╗ ██████╗     ███████╗██╗  ██╗\n");
    print("  ██╔════╝╚██╗██╔╝██╔═══██╗██║   ██║██╔════╝     ██╔════╝██║  ██║\n");
    print("  █████╗   ╚███╔╝ ██║   ██║██║   ██║███████╗     ███████╗███████║\n");
    print("  ██╔══╝   ██╔██╗ ██║   ██║╚██╗ ██╔╝██╔═══██╗    ╚════██║██╔══██║\n");
    print("  ███████╗██╔╝ ██╗╚██████╔╝ ╚████╔╝ ╚██████╔╝    ███████║██║  ██║\n");
    print("  ╚══════╝╚═╝  ╚═╝ ╚═════╝   ╚═══╝   ╚═════╝     ╚══════╝╚═╝  ╚═╝\n");
    print("═══════════════════════════════════════════════════════════════════\n");
    print("  The Voice - ExoV6 User Shell (Phase 11)\n");
    print("═══════════════════════════════════════════════════════════════════\n");
    print("\n");

    /* Initialize exception handling */
    libos_exception_init();

    print("Shell uses spawn() instead of fork()+exec()\n");
    print("  Kernel provides: env_create, page_map, env_run, IPC\n");
    print("  LibOS provides: ELF loading, stack setup, file I/O\n");
    print("\n");

    /* Run demo */
    run_demo();

    /* Idle loop */
    print("\n");
    print("Shell entering idle (console input not implemented yet)...\n");
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

/* ═══════════════════════════════════════════════════════════════════════════
 * PEDAGOGICAL SUMMARY
 *
 * This shell demonstrates the key differences between UNIX V6 and ExoV6:
 *
 * UNIX V6 Shell (fork+exec):
 *   1. fork() - Kernel clones parent's entire address space
 *   2. Child calls exec() - Kernel parses ELF, replaces address space
 *   3. Parent calls wait() - Kernel tracks process hierarchy
 *
 * ExoV6 Shell (spawn):
 *   1. spawn() - LibOS opens ELF via IPC to fs_srv
 *   2. LibOS creates blank env via sys_env_create
 *   3. LibOS parses ELF, maps pages via sys_page_map
 *   4. LibOS sets up stack (argc/argv)
 *   5. LibOS starts child via sys_env_run
 *
 * The kernel in ExoV6 has NO IDEA:
 *   - What an ELF file is
 *   - What argc/argv mean
 *   - What a "shell" is
 *   - What "executing a program" means
 *
 * All of that is POLICY defined by the LibOS.
 * The kernel only provides MECHANISM: pages, address spaces, CPU time.
 *
 * TODO for full shell:
 *   - SYS_getc: Console input character
 *   - SYS_wait: Wait for child to exit
 *   - Pipes: IPC-based pipe server
 *   - Redirection: FD table manipulation
 * ═══════════════════════════════════════════════════════════════════════════ */

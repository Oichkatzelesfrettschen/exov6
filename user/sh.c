/**
 * @file sh.c
 * @brief ExoV6 Shell - "The Voice" (Phase 11b - Interactive)
 *
 * ╔═══════════════════════════════════════════════════════════════════════════╗
 * ║  LIONS' COMMENTARY FOR THE POST-MONOLITHIC AGE                            ║
 * ║                                                                           ║
 * ║  LESSON: The shell is the COMPLETE demonstration of exokernel design.     ║
 * ║                                                                           ║
 * ║  Components working together:                                             ║
 * ║    - sys_cgetc()   : The Sense (keyboard input)                          ║
 * ║    - spawn()       : The Hands (process creation)                        ║
 * ║    - sys_env_wait(): The Patience (synchronization)                      ║
 * ║    - fs_srv IPC    : The Memory (file access)                            ║
 * ║                                                                           ║
 * ║  The KERNEL provides only:                                                ║
 * ║    - Page allocation/mapping                                              ║
 * ║    - Environment create/run/wait                                          ║
 * ║    - IPC send/receive                                                     ║
 * ║    - Console character I/O                                                ║
 * ║                                                                           ║
 * ║  The LIBOS provides:                                                      ║
 * ║    - ELF parsing and loading                                              ║
 * ║    - File abstraction (via fs_srv)                                        ║
 * ║    - Command line parsing                                                 ║
 * ║    - Process model (spawn vs fork+exec)                                   ║
 * ╚═══════════════════════════════════════════════════════════════════════════╝
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

/* syscalls */
extern int sys_cgetc(void);
extern int sys_env_wait(int child_pid);

/* spawn() - Process creation */
extern int spawn(const char *path, char **argv);

/* ═══════════════════════════════════════════════════════════════════════════
 * Configuration
 * ═══════════════════════════════════════════════════════════════════════════ */

#define MAXLINE 128
#define MAXARGS 16

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

static int strcmp_sh(const char *a, const char *b) {
    while (*a && *b && *a == *b) {
        a++;
        b++;
    }
    return *a - *b;
}

static int strlen_sh(const char *s) {
    int len = 0;
    while (*s++) len++;
    return len;
}

/* ═══════════════════════════════════════════════════════════════════════════
 * Command Line Buffer
 * ═══════════════════════════════════════════════════════════════════════════ */

static char linebuf[MAXLINE];

/* ═══════════════════════════════════════════════════════════════════════════
 * readline() - Read a line from the console
 *
 * LIONS' LESSON: This is where the shell "hears".
 * sys_cgetc() blocks until a character is available.
 * The kernel wakes us when keyboard IRQ fires.
 * ═══════════════════════════════════════════════════════════════════════════ */

static void readline(const char *prompt) {
    print(prompt);

    int i = 0;
    while (i < MAXLINE - 1) {
        int c = sys_cgetc();

        if (c < 0) {
            /* Error or killed */
            linebuf[0] = '\0';
            return;
        }

        if (c == '\r' || c == '\n') {
            /* End of line */
            print("\n");
            linebuf[i] = '\0';
            return;
        }

        if (c == 127 || c == '\b' || c == 8) {
            /* Backspace */
            if (i > 0) {
                i--;
                print("\b \b");  /* Erase character on screen */
            }
            continue;
        }

        if (c == 21) {  /* Ctrl-U: kill line */
            while (i > 0) {
                i--;
                print("\b \b");
            }
            continue;
        }

        if (c >= 32 && c < 127) {
            /* Printable character */
            linebuf[i++] = (char)c;
            /* Echo */
            char echo[2] = {(char)c, '\0'};
            print(echo);
        }
    }

    linebuf[i] = '\0';
}

/* ═══════════════════════════════════════════════════════════════════════════
 * parse_args() - Split command line into arguments
 * ═══════════════════════════════════════════════════════════════════════════ */

static int parse_args(char *line, char **argv) {
    int argc = 0;
    char *p = line;

    /* Skip leading whitespace */
    while (*p == ' ' || *p == '\t') p++;

    while (*p && argc < MAXARGS - 1) {
        argv[argc++] = p;

        /* Find end of argument */
        while (*p && *p != ' ' && *p != '\t') p++;

        if (*p) {
            *p++ = '\0';  /* Null-terminate */
            /* Skip whitespace */
            while (*p == ' ' || *p == '\t') p++;
        }
    }

    argv[argc] = 0;  /* Null-terminate argv array */
    return argc;
}

/* ═══════════════════════════════════════════════════════════════════════════
 * Built-in Commands
 * ═══════════════════════════════════════════════════════════════════════════ */

static void cmd_help(void) {
    print("\n");
    print("ExoV6 Shell - Built-in Commands:\n");
    print("  help      - Show this help\n");
    print("  about     - About ExoV6\n");
    print("  exit      - Exit the shell\n");
    print("\n");
    print("External Commands:\n");
    print("  /path     - Run program at path (e.g., /hello)\n");
    print("\n");
    print("The shell uses spawn() instead of fork()+exec().\n");
    print("All file access goes through fs_srv via IPC.\n");
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
    print("  KERNEL (Mechanism):  pages, address spaces, CPU time, IPC\n");
    print("  LIBOS  (Policy):     files, processes, sockets, memory layout\n");
    print("\n");
}

/* ═══════════════════════════════════════════════════════════════════════════
 * run_external() - Spawn an external program
 *
 * LIONS' LESSON: This is where spawn() vs fork()+exec() shines.
 *
 * UNIX V6:
 *   pid = fork();
 *   if (pid == 0) exec(path, argv);
 *   wait();
 *
 * ExoV6:
 *   pid = spawn(path, argv);
 *   sys_env_wait(pid);
 *
 * No address space cloning. No zombie complexity. Just pure creation.
 * ═══════════════════════════════════════════════════════════════════════════ */

static void run_external(char *path, char **argv) {
    print("Spawning: ");
    print(path);
    print("\n");

    int child_pid = spawn(path, argv);

    if (child_pid < 0) {
        print("sh: spawn failed for ");
        print(path);
        print("\n");
        print("    (Is fs_srv running? Does the file exist?)\n");
        return;
    }

    print("sh: child PID ");
    print_int(child_pid);
    print("\n");

    /* Wait for child to exit */
    print("sh: waiting for child...\n");
    int exit_status = sys_env_wait(child_pid);

    print("sh: child exited with status ");
    print_int(exit_status);
    print("\n");
}

/* ═══════════════════════════════════════════════════════════════════════════
 * execute() - Process and execute a command
 * ═══════════════════════════════════════════════════════════════════════════ */

static int execute(char *line) {
    char *argv[MAXARGS];
    int argc = parse_args(line, argv);

    if (argc == 0) {
        return 1;  /* Empty line, continue */
    }

    /* Built-in commands */
    if (strcmp_sh(argv[0], "help") == 0) {
        cmd_help();
        return 1;
    }

    if (strcmp_sh(argv[0], "about") == 0) {
        cmd_about();
        return 1;
    }

    if (strcmp_sh(argv[0], "exit") == 0) {
        print("Goodbye.\n");
        return 0;  /* Exit shell */
    }

    /* External commands */
    run_external(argv[0], argv);
    return 1;
}

/* ═══════════════════════════════════════════════════════════════════════════
 * Main Entry Point - The Read-Eval-Print Loop (REPL)
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
    print("  The Voice - ExoV6 Interactive Shell (Phase 11b)\n");
    print("═══════════════════════════════════════════════════════════════════\n");
    print("\n");

    /* Initialize exception handling */
    libos_exception_init();

    print("Type 'help' for commands, 'exit' to quit.\n");
    print("\n");

    /* The REPL - Read, Eval, Print, Loop */
    while (1) {
        readline("$ ");

        if (linebuf[0] == '\0') {
            continue;  /* Empty line */
        }

        if (!execute(linebuf)) {
            break;  /* exit command */
        }
    }

    /* Clean exit */
    print("Shell terminated.\n");

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
 * This interactive shell demonstrates the COMPLETE exokernel architecture:
 *
 * 1. THE SENSE (sys_cgetc):
 *    Keyboard IRQ → Kernel tty buffer → sleep/wakeup → Shell reads char
 *
 * 2. THE HANDS (spawn):
 *    Shell → open() via IPC → fs_srv → VirtIO disk
 *    Shell → elf_load_into_child() → allocate pages, map segments
 *    Shell → sys_env_run() → child starts executing
 *
 * 3. THE PATIENCE (sys_env_wait):
 *    Parent sleeps → Child runs → Child exits (wakeup) → Parent reaps zombie
 *
 * 4. THE MEMORY (fs_client):
 *    All file operations are IPC messages to the File Server.
 *    The kernel never sees file paths or inodes.
 *
 * Compare to UNIX V6:
 *   - V6 kernel: ~10,000 lines, complex fork/exec/wait/file handling
 *   - ExoV6 kernel: Raw primitives only, LibOS handles everything else
 *
 * "Simplicity is the ultimate sophistication." - Leonardo da Vinci
 * ═══════════════════════════════════════════════════════════════════════════ */

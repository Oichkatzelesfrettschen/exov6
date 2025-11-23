/**
 * @file exo_echo.c
 * @brief ExoV6 Echo Utility (Phase 11.7)
 *
 * The simplest possible utility - just echoes arguments to stdout.
 * Demonstrates fd_write() to console.
 */

#include <stdint.h>
#include <types.h>
#include <fd.h>

/* External */
extern void libos_exception_init(void);

/* ═══════════════════════════════════════════════════════════════════════════
 * Helpers
 * ═══════════════════════════════════════════════════════════════════════════ */

static int strlen_echo(const char *s) {
    int len = 0;
    while (*s++) len++;
    return len;
}

/* ═══════════════════════════════════════════════════════════════════════════
 * Main
 * ═══════════════════════════════════════════════════════════════════════════ */

int main(int argc, char **argv) {
    fd_init();
    libos_exception_init();

    /* Echo all arguments */
    for (int i = 1; i < argc; i++) {
        if (i > 1) {
            fd_write(FD_STDOUT, " ", 1);  /* Space between args */
        }
        fd_write(FD_STDOUT, argv[i], strlen_echo(argv[i]));
    }

    /* Newline at end */
    fd_write(FD_STDOUT, "\n", 1);

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

/**
 * @file rfork.h
 * @brief BSD/Plan 9-compatible rfork Interface
 *
 * Cleanroom implementation of rfork for FeuerBird exokernel.
 * Provides configurable process creation (BSD variant).
 *
 * rfork provides:
 * - Configurable resource sharing (Plan 9 heritage)
 * - Thread creation (RFMEM | RFTHREAD)
 * - Process group control
 * - Memory space copying/sharing
 */
#pragma once

#include <stdint.h>

/**
 * rfork flags (BSD-compatible values)
 *
 * These originate from Plan 9 and were adopted by FreeBSD.
 * Some have been deprecated in favor of pthreads/clone.
 */

/* Process creation */
#define RFPROC          (1 << 4)    /* Change child (else changes self) */
#define RFNOWAIT        (1 << 6)    /* Child is dissociated from parent */
#define RFCFDG          (1 << 12)   /* Close all fds (control fds go) */
#define RFSIGSHARE      (1 << 14)   /* Share signal handlers (FreeBSD) */
#define RFLINUXTHPN     (1 << 16)   /* Linux thread notification (FreeBSD) */
#define RFTSIGZMB       (1 << 19)   /* Use SIGUSR1 on thread exit (FreeBSD) */
#define RFSPAWN         (1 << 31)   /* Spawn mode (for posix_spawn) */

/* Resource sharing */
#define RFNAMEG         (1 << 0)    /* New name group (Plan 9) */
#define RFENVG          (1 << 1)    /* New environment group (Plan 9) */
#define RFFDG           (1 << 2)    /* Copy file descriptors */
#define RFNOTEG         (1 << 3)    /* New note group (Plan 9) */
#define RFMEM           (1 << 5)    /* Share memory space */
#define RFCNAMEG        (1 << 10)   /* Zero name group (Plan 9) */
#define RFCENVG         (1 << 11)   /* Zero environment group (Plan 9) */

/* Threading (FreeBSD extensions) */
#define RFTHREAD        (1 << 13)   /* Create thread, not process */
#define RFPID           (1 << 15)   /* Specific PID (internal) */

/**
 * BSD pdfork flags (for process descriptor fork)
 */
#define PD_DAEMON       0x01        /* Process becomes a daemon */
#define PD_CLOEXEC      0x02        /* Close process descriptor on exec */

/**
 * Create a new process/thread with configurable sharing
 *
 * @param flags         RFORK_* flags
 * @return              PID in parent, 0 in child, -errno on error
 *
 * With RFPROC: creates new process
 * Without RFPROC: modifies current process (like unshare)
 * With RFMEM|RFTHREAD: creates thread
 */
int sys_rfork(int flags);

/**
 * Create process with process descriptor (FreeBSD)
 *
 * @param fdp           Output: process descriptor fd
 * @param flags         PD_* flags
 * @return              PID in parent, 0 in child, -errno on error
 */
int sys_pdfork(int *fdp, int flags);

/**
 * Get process descriptor from PID (FreeBSD)
 *
 * @param pid           Process ID
 * @param flags         Reserved (must be 0)
 * @return              Process descriptor fd, or -errno on error
 */
int sys_pdgetpid(int fd, int *pidp);

/**
 * Kill process via descriptor (FreeBSD)
 *
 * @param fd            Process descriptor
 * @param signum        Signal to send
 * @return              0 on success, -errno on error
 */
int sys_pdkill(int fd, int signum);

/**
 * Translate rfork flags to clone flags
 *
 * @param rfork_flags   rfork flags
 * @return              Equivalent clone flags
 */
uint64_t rfork_to_clone_flags(int rfork_flags);

/**
 * Initialize rfork subsystem
 */
void rfork_init(void);


/**
 * @file clone.h
 * @brief Linux-compatible clone Interface
 *
 * Cleanroom implementation of clone for FeuerBird exokernel.
 * Provides configurable process/thread creation.
 *
 * clone provides:
 * - Configurable resource sharing (memory, files, signals)
 * - Thread creation (CLONE_VM | CLONE_THREAD)
 * - Container namespaces (CLONE_NEWNS, CLONE_NEWPID, etc.)
 * - PID namespace separation
 */
#pragma once

#include <stdint.h>

/**
 * Clone flags (Linux-compatible values)
 */

/* Signal handling */
#define CLONE_SIGHAND       0x00000800  /* Share signal handlers */
#define CLONE_PTRACE        0x00002000  /* Continue tracing child */
#define CLONE_VFORK         0x00004000  /* Set if parent wants child to wake on mm_release */

/* Resource sharing */
#define CLONE_VM            0x00000100  /* Share address space */
#define CLONE_FS            0x00000200  /* Share cwd, root, umask */
#define CLONE_FILES         0x00000400  /* Share file descriptor table */
#define CLONE_THREAD        0x00010000  /* Same thread group as parent */
#define CLONE_SYSVSEM       0x00040000  /* Share SysV semaphore undo */
#define CLONE_IO            0x80000000  /* Clone I/O context */

/* ID settings */
#define CLONE_SETTLS        0x00080000  /* Set TLS descriptor */
#define CLONE_PARENT_SETTID 0x00100000  /* Set parent TID in parent memory */
#define CLONE_CHILD_SETTID  0x01000000  /* Set child TID in child memory */
#define CLONE_CHILD_CLEARTID 0x00200000 /* Clear child TID on exit */
#define CLONE_DETACHED      0x00400000  /* Unused, ignored */
#define CLONE_UNTRACED      0x00800000  /* No PTRACE_ATTACH allowed */

/* Namespace creation (container support) */
#define CLONE_NEWNS         0x00020000  /* New mount namespace */
#define CLONE_NEWCGROUP     0x02000000  /* New cgroup namespace */
#define CLONE_NEWUTS        0x04000000  /* New UTS namespace */
#define CLONE_NEWIPC        0x08000000  /* New IPC namespace */
#define CLONE_NEWUSER       0x10000000  /* New user namespace */
#define CLONE_NEWPID        0x20000000  /* New PID namespace */
#define CLONE_NEWNET        0x40000000  /* New network namespace */

/* pidfd support (Linux 5.2+) */
#define CLONE_PIDFD         0x00001000  /* Create pidfd for child */

/* Clear/set ITIMER_REAL (Linux 5.9+) */
#define CLONE_CLEAR_SIGHAND 0x100000000ULL  /* Clear any signal handler */

/* Signal to send on child exit (low 8 bits) */
#define CLONE_EXIT_SIGNAL_MASK 0x000000ff

/**
 * clone3 arguments structure (Linux 5.3+)
 */
struct clone_args {
    uint64_t flags;         /* Clone flags */
    uint64_t pidfd;         /* Where to store pidfd (CLONE_PIDFD) */
    uint64_t child_tid;     /* Where to store child TID */
    uint64_t parent_tid;    /* Where to store parent TID */
    uint64_t exit_signal;   /* Signal to send on exit */
    uint64_t stack;         /* Stack pointer for child */
    uint64_t stack_size;    /* Stack size */
    uint64_t tls;           /* TLS pointer */
    uint64_t set_tid;       /* Array of TIDs to use in new namespaces */
    uint64_t set_tid_size;  /* Number of TIDs */
    uint64_t cgroup;        /* cgroup fd (CLONE_INTO_CGROUP) */
};

/**
 * Clone result (for pidfd)
 */
struct clone_result {
    int pid;                /* Child PID */
    int pidfd;              /* pidfd if CLONE_PIDFD */
};

/**
 * Create a new process or thread with configurable sharing
 *
 * @param flags         CLONE_* flags
 * @param stack         Stack pointer for child (NULL = share with parent)
 * @param ptid          Parent TID pointer (CLONE_PARENT_SETTID)
 * @param tls           TLS pointer (CLONE_SETTLS)
 * @param ctid          Child TID pointer (CLONE_CHILD_SETTID)
 * @return              PID in parent, 0 in child, -errno on error
 */
int sys_clone(uint64_t flags, void *stack, int *ptid, void *tls, int *ctid);

/**
 * Create a new process or thread (clone3 interface)
 *
 * @param args          Clone arguments
 * @param size          Size of args structure
 * @return              PID in parent, 0 in child, -errno on error
 */
int sys_clone3(struct clone_args *args, uint64_t size);

/**
 * Fork the current process (clone wrapper)
 * Equivalent to clone(SIGCHLD, 0, NULL, NULL, NULL)
 *
 * @return              PID in parent, 0 in child, -errno on error
 */
int sys_fork_clone(void);

/**
 * Vfork the current process (clone wrapper)
 * Equivalent to clone(CLONE_VFORK | CLONE_VM | SIGCHLD, 0, NULL, NULL, NULL)
 *
 * @return              PID in parent, 0 in child, -errno on error
 */
int sys_vfork_clone(void);

/**
 * Set TID address for CLONE_CHILD_CLEARTID
 *
 * @param tidptr        Address to clear on exit
 * @return              Caller's TID
 */
int sys_set_tid_address(int *tidptr);

/**
 * Unshare resources without creating new process
 *
 * @param flags         CLONE_* flags specifying what to unshare
 * @return              0 on success, -errno on error
 */
int sys_unshare(uint64_t flags);

/**
 * Enter a namespace via file descriptor
 *
 * @param fd            Namespace file descriptor
 * @param nstype        CLONE_NEW* type to validate
 * @return              0 on success, -errno on error
 */
int sys_setns(int fd, int nstype);

/**
 * Initialize clone subsystem
 */
void clone_init(void);


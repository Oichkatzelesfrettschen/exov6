/**
 * @file kernel_stubs.c
 * @brief Stub implementations for missing kernel functions
 *
 * These are temporary implementations to satisfy the linker.
 * They should be replaced with proper implementations as development progresses.
 */

#include "types.h"
#include "defs.h"
#include <stdarg.h>
#include <stddef.h>

/* ========================================================================
 * Standard C Library Functions (not provided by string.c)
 * ======================================================================== */

/**
 * Simplified snprintf for kernel use
 * TODO: Replace with full implementation
 */
int snprintf(char *str, size_t size, const char *format, ...)
{
    if (!str || size == 0)
        return 0;

    va_list args;
    va_start(args, format);

    /* Very simple implementation - just copy format string for now */
    size_t i = 0;
    const char *p = format;
    while (*p && i < size - 1) {
        str[i++] = *p++;
    }
    str[i] = '\0';

    va_end(args);
    return i;
}

/**
 * Kernel malloc - uses kalloc for now
 * TODO: Implement proper malloc/free with size tracking
 */
void *malloc(size_t size)
{
    /* Use kalloc for page-aligned allocations */
    if (size <= PGSIZE) {
        return kalloc();
    }
    /* For larger allocations, allocate multiple pages */
    /* TODO: Implement proper malloc */
    return (void *)0;
}

/**
 * Kernel free - uses kfree for now
 * TODO: Implement proper malloc/free with size tracking
 */
void free(void *ptr)
{
    if (ptr) {
        kfree((char *)ptr);
    }
}

/* ========================================================================
 * File Operations (stubs until file system is fully integrated)
 * ======================================================================== */

struct file;
struct stat;

/**
 * Allocate a file descriptor
 * TODO: Implement when file table is ready
 */
struct file *filealloc(void)
{
    return (struct file *)0;
}

/**
 * Duplicate a file descriptor
 * TODO: Implement when file table is ready
 */
struct file *filedup(struct file *f)
{
    (void)f;
    return (struct file *)0;
}

/**
 * Close a file descriptor
 * TODO: Implement when file table is ready
 */
void fileclose(struct file *f)
{
    (void)f;
}

/**
 * Get file status
 * TODO: Implement when file table is ready
 */
int filestat(struct file *f, struct stat *st)
{
    (void)f;
    (void)st;
    return -1;
}

/* ========================================================================
 * Process Operations (stubs until process management is ready)
 * ======================================================================== */

/**
 * Spawn a new process
 * TODO: Implement when process management is ready
 */
int proc_spawn(void (*fn)(void))
{
    (void)fn;
    return -1;
}

/**
 * Wait for process
 * TODO: Implement when process management is ready
 */
int proc_wait(void)
{
    return -1;
}

/**
 * Exit current process
 * TODO: Implement when process management is ready
 */
void proc_exit(int status)
{
    (void)status;
    /* Infinite loop for now */
    for (;;)
        ;
}

/**
 * Wait for child process
 * TODO: Implement when process management is ready
 */
int wait(void)
{
    return -1;
}

/**
 * Send signal to process
 * TODO: Implement when signal handling is ready
 */
int kill(int pid)
{
    (void)pid;
    return -1;
}

/* ========================================================================
 * Console/TTY Operations (stubs)
 * ======================================================================== */

/**
 * TTY echo
 * TODO: Implement when TTY is ready
 */
void ttypecho(int c)
{
    (void)c;
}

/**
 * Device switch table
 * TODO: Define when device framework is ready
 */
struct devsw {
    int (*read)(void);
    int (*write)(void);
};

struct devsw devsw[10]; /* Placeholder */

/* ========================================================================
 * Kernel Printf (stub)
 * ======================================================================== */

/**
 * Kernel printf
 * TODO: Implement proper kernel printf
 */
int kprintf(const char *fmt, ...)
{
    (void)fmt;
    return 0;
}

/* ========================================================================
 * Lattice IPC Operations (stubs)
 * ======================================================================== */

/**
 * Sign lattice message
 * TODO: Implement when lattice IPC is ready
 */
int lattice_sign(void *msg, size_t len, void *sig)
{
    (void)msg;
    (void)len;
    (void)sig;
    return 0;
}

/**
 * Send lattice channel message
 * TODO: Implement when lattice IPC is ready
 */
int lattice_channel_send(void *chan, void *msg, size_t len)
{
    (void)chan;
    (void)msg;
    (void)len;
    return 0;
}

/**
 * Initialize lattice crypto
 * TODO: Implement when lattice crypto is ready
 */
void lattice_crypto_init(void)
{
    /* Nothing for now */
}

/**
 * Initialize lattice channel
 * TODO: Implement when lattice IPC is ready
 */
int lattice_channel_init(void *chan)
{
    (void)chan;
    return 0;
}

/* ========================================================================
 * Scheduler Operations (stubs)
 * ======================================================================== */

/**
 * Beatty scheduler operations
 * TODO: Implement when scheduler is ready
 */
struct exo_sched_ops {
    void (*init)(void);
    void (*schedule)(void);
};

static struct exo_sched_ops beatty_ops = {
    .init = 0,
    .schedule = 0,
};

static struct exo_sched_ops dag_ops = {
    .init = 0,
    .schedule = 0,
};

struct exo_sched_ops *beatty_sched_ops(void)
{
    return &beatty_ops;
}

struct exo_sched_ops *dag_sched_ops(void)
{
    return &dag_ops;
}

/* ========================================================================
 * System Call (stub)
 * ======================================================================== */

/**
 * Timed receive system call
 * TODO: Implement when IPC is ready
 */
int sys_exo_recv_timed(void)
{
    return -1;
}

/* ========================================================================
 * Capability Validation (stub)
 * ======================================================================== */

#include "cap.h"

/**
 * Unified capability validation
 * TODO: Implement properly in capability system
 */
cap_validation_result_t cap_validate_unified(cap_id_t id, struct cap_entry *out_entry_if_valid)
{
    (void)id;
    (void)out_entry_if_valid;
    return VALIDATION_INVALID_ID; /* Defined in cap.h */
}

/* ========================================================================
 * Lock Operations (exo_lock.h inline wrappers call these)
 * ======================================================================== */

/* Forward declaration of exo_lock type */
struct exo_lock;

/* Need to include exo_lock.h for type definitions */
#include "exo_lock.h"

/**
 * Initialize exo_lock
 * TODO: Implement actual lock initialization
 */
void exo_lock_init(struct exo_lock *lock, exo_lock_type_t type, const char *name, uint32_t level)
{
    (void)lock;
    (void)type;
    (void)name;
    (void)level;
}

/**
 * Acquire exo_lock
 * TODO: Implement actual lock acquisition
 */
void exo_lock_acquire(struct exo_lock *lock)
{
    (void)lock;
}

/**
 * Release exo_lock
 * TODO: Implement actual lock release
 */
void exo_lock_release(struct exo_lock *lock)
{
    (void)lock;
}

/**
 * Check if holding exo_lock
 * TODO: Implement actual lock check
 */
int exo_lock_holding(struct exo_lock *lock)
{
    (void)lock;
    return 0;
}

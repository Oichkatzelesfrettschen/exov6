/**
 * @file kernel_core_stubs.c
 * @brief Minimal stub implementations for core kernel functions
 *
 * These stubs allow the kernel to link while the kernel/sync/ and kernel/sched/
 * subdirectories are being refactored to resolve type conflicts. Each stub
 * implements the bare minimum needed for a non-functional but linkable kernel.
 *
 * TODO: Remove this file once sync/ and sched/ subdirectories are properly
 * refactored and integrated.
 */

#include "defs.h"
#include "proc.h"
#include "spinlock.h"
#include <stddef.h>
#include <stdatomic.h>
#include <exo.h>  /* For exo_cap type */

/* Process table and scheduler lock - required by defs.h declarations */
struct ptable ptable;
struct spinlock sched_lock;

/* Spinlock stubs using ticketlock */
void initlock(struct spinlock *lk, const char *name) {
    atomic_store(&lk->ticket.head, 0);
    atomic_store(&lk->ticket.tail, 0);
    lk->name = name;
    lk->cpu = NULL;
}

void acquire(struct spinlock *lk) {
    /* Stub: acquire ticket and spin until served */
    uint_least16_t ticket = atomic_fetch_add(&lk->ticket.tail, 1);
    while (atomic_load(&lk->ticket.head) != ticket) {
        /* Spin */
    }
}

void release(struct spinlock *lk) {
    /* Stub: advance head to serve next waiter */
    atomic_fetch_add(&lk->ticket.head, 1);
}

int holding(struct spinlock *lk) {
    /* Stub: check if lock is currently held (head != tail means waiters) */
    return atomic_load(&lk->ticket.head) != atomic_load(&lk->ticket.tail);
}

void pushcli(void) {
    /* Stub: disable interrupts would go here */
}

void popcli(void) {
    /* Stub: restore interrupt state would go here */
}

/* Process management stubs */
static struct proc dummy_proc;

struct proc *myproc(void) {
    return &dummy_proc;
}

struct cpu *mycpu(void) {
    return NULL;
}

int fork(void) {
    return -1;  /* Fork not implemented */
}

int exec(const char *path, char *const argv[]) {
    (void)path;
    (void)argv;
    return -1;  /* Exec not implemented */
}

_Noreturn void exit(int status) {
    (void)status;
    for (;;) {
        /* Never returns */
    }
}

void sleep(void *chan, struct spinlock *lk) {
    (void)chan;
    (void)lk;
    /* Stub: sleep not implemented */
}

void wakeup(void *chan) {
    (void)chan;
    /* Stub: wakeup not implemented */
}

/* Kernel-internal sleep/exit functions (Phase 4B) */
_Noreturn void kexit(int status) {
    /* Kernel exit - call the standard exit stub */
    exit(status);
}

void ksleep(void *chan, struct spinlock *lk) {
    /* Kernel sleep wrapper - call the standard sleep stub */
    sleep(chan, lk);
}

/* Capability table: Real implementations in ipc/cap_table.c and ipc/cap.c */
/* cap_table_alloc, cap_table_lookup, cap_table_inc, cap_table_dec - see ipc/cap_table.c */
/* cap_new, cap_verify - see ipc/cap.c */

int cap_send(exo_cap cap, const void *buf, uint64_t len) {
    (void)cap;
    (void)buf;
    (void)len;
    return -1;  /* Not implemented - requires full IPC channel support */
}

/* Memory management stubs */
void kfree(char *ptr) {
    (void)ptr;
    /* Stub: memory free not implemented */
}

char *kalloc(void) {
    return NULL;  /* Stub: memory allocation not implemented */
}

/* Inode locking stubs */
void ilock(struct inode *ip) {
    (void)ip;
}

void iunlock(struct inode *ip) {
    (void)ip;
}

/* Console output stub */
void cprintf(const char *fmt, ...) {
    (void)fmt;
    /* Stub: console printf not implemented */
}

/* UART/serial output stub for TTY */
void uartputc(int c) {
    (void)c;
    /* Stub: UART output not implemented */
}

/* Kernel panic stub */
_Noreturn void panic(const char *s) {
    (void)s;
    /* Stub: panic - halt system */
    while (1);
}

/* Stream registration stub */
void exo_stream_register(struct exo_stream *s) {
    (void)s;
}

/* Capability verification: Real implementation in ipc/cap.c */

/* LAPIC end-of-interrupt stub */
void lapiceoi(void) {
    /* Stub: acknowledge interrupt to LAPIC */
}

/* Cache line size for spinlock alignment */
size_t cache_line_size = 64;  /* Default to common x86_64 cache line size */

void detect_cache_line_size(void) {
    /* Use CPUID to detect actual cache line size
     * For now, default to 64 bytes (common for modern x86_64) */
    cache_line_size = 64;
}

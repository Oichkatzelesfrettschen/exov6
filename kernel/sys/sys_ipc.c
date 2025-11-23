/**
 * @file sys_ipc.c
 * @brief Synchronous IPC Implementation (Phase 9)
 *
 * This file implements the core IPC primitives for the exokernel:
 *   - sys_ipc_send(): Send a message to another process
 *   - sys_ipc_recv(): Receive a message (blocking)
 *
 * Design Goals:
 *   1. Simple synchronous semantics (like L4/seL4)
 *   2. Register-based for small messages (fast path)
 *   3. Uses per-process mailbox for queueing
 *   4. Blocking receive with sleep/wakeup
 *
 * Message Format (in registers):
 *   arg0: target_pid (send) or source_pid pointer (recv)
 *   arg1: value word 0
 *   arg2: value word 1
 *   arg3: value word 2 (optional: shared page VA)
 */

#include <types.h>
#include <defs.h>
#include <param.h>
#include <proc.h>
#include <spinlock.h>

// External declarations
extern struct ptable ptable;
extern int argint(int n, int *ip);
extern int arguint64(int n, uint64_t *ip);

// Forward declarations
static struct proc* find_proc_by_pid(int pid);
static int mailbox_enqueue(struct mailbox *mb, int sender_pid,
                           uint64_t w0, uint64_t w1, uint64_t w2);
static int mailbox_dequeue(struct mailbox *mb, int *sender_pid,
                           uint64_t *w0, uint64_t *w1, uint64_t *w2);
static int mailbox_is_empty(struct mailbox *mb);

// ═══════════════════════════════════════════════════════════════════════════
// Helper Functions
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Find a process by PID
 * Must be called with ptable.lock held or interrupts disabled
 */
static struct proc* find_proc_by_pid(int pid) {
    struct proc *p;
    for (p = ptable.proc; p < &ptable.proc[NPROC]; p++) {
        if (p->pid == pid && p->state != UNUSED && p->state != ZOMBIE) {
            return p;
        }
    }
    return 0;
}

/**
 * Check if mailbox is empty
 */
static int mailbox_is_empty(struct mailbox *mb) {
    return mb->r == mb->w;
}

/**
 * Check if mailbox is full
 */
static int mailbox_is_full(struct mailbox *mb) {
    return ((mb->w + 1) % MAILBOX_BUFSZ) == mb->r;
}

/**
 * Enqueue a message into a mailbox
 * Returns 0 on success, -1 if full
 */
static int mailbox_enqueue(struct mailbox *mb, int sender_pid,
                           uint64_t w0, uint64_t w1, uint64_t w2) {
    if (mailbox_is_full(mb)) {
        return -1;  // Mailbox full
    }

    uint32_t idx = mb->w % MAILBOX_BUFSZ;
    mb->buf[idx].msg.badge = (uint64_t)sender_pid;
    mb->buf[idx].msg.w0 = w0;
    mb->buf[idx].msg.w1 = w1;
    mb->buf[idx].msg.w2 = w2;
    mb->buf[idx].msg.w3 = 0;  // Reserved

    // Memory barrier before updating write pointer
    __sync_synchronize();
    mb->w = (mb->w + 1) % MAILBOX_BUFSZ;

    return 0;
}

/**
 * Dequeue a message from a mailbox
 * Returns 0 on success, -1 if empty
 */
static int mailbox_dequeue(struct mailbox *mb, int *sender_pid,
                           uint64_t *w0, uint64_t *w1, uint64_t *w2) {
    if (mailbox_is_empty(mb)) {
        return -1;  // Mailbox empty
    }

    uint32_t idx = mb->r % MAILBOX_BUFSZ;
    *sender_pid = (int)mb->buf[idx].msg.badge;
    *w0 = mb->buf[idx].msg.w0;
    *w1 = mb->buf[idx].msg.w1;
    *w2 = mb->buf[idx].msg.w2;

    // Memory barrier before updating read pointer
    __sync_synchronize();
    mb->r = (mb->r + 1) % MAILBOX_BUFSZ;

    return 0;
}

// ═══════════════════════════════════════════════════════════════════════════
// System Call Implementations
// ═══════════════════════════════════════════════════════════════════════════

/**
 * sys_ipc_send - Send a message to another process
 *
 * Arguments (in registers):
 *   arg0: target_pid - Destination process ID
 *   arg1: w0 - First data word
 *   arg2: w1 - Second data word
 *   arg3: w2 - Third data word (can be shared buffer VA)
 *
 * Returns:
 *   0 on success
 *  -1 if target not found
 *  -2 if target mailbox full
 */
int sys_ipc_send(void) {
    int target_pid;
    uint64_t w0, w1, w2;

    // Extract arguments
    if (argint(0, &target_pid) < 0) return -1;
    if (arguint64(1, &w0) < 0) return -1;
    if (arguint64(2, &w1) < 0) return -1;
    if (arguint64(3, &w2) < 0) w2 = 0;  // Optional

    struct proc *sender = myproc();
    struct proc *target;

    // Find target process
    acquire_compat(&ptable.lock);
    target = find_proc_by_pid(target_pid);

    if (!target) {
        release_compat(&ptable.lock);
        return -1;  // Target not found
    }

    // Ensure target has a mailbox
    if (!target->mailbox || !target->mailbox->inited) {
        release_compat(&ptable.lock);
        return -1;  // Target has no mailbox
    }

    // Lock the target's mailbox
    acquire(&target->mailbox->lock);
    release_compat(&ptable.lock);

    // Enqueue message
    int result = mailbox_enqueue(target->mailbox, sender->pid, w0, w1, w2);

    if (result < 0) {
        release(&target->mailbox->lock);
        return -2;  // Mailbox full
    }

    release(&target->mailbox->lock);

    // Wake up target if it's waiting for IPC
    // Use ipc_chan field as the sleep channel
    wakeup(target->mailbox);

    return 0;
}

/**
 * sys_ipc_recv - Receive a message (blocking)
 *
 * Arguments (in registers):
 *   arg0: sender_pid_ptr - Pointer to store sender's PID
 *   arg1: w0_ptr - Pointer to store first data word
 *   arg2: w1_ptr - Pointer to store second data word
 *   arg3: w2_ptr - Pointer to store third data word
 *
 * Returns:
 *   0 on success
 *  -1 on error (invalid arguments)
 *
 * Note: This call blocks until a message is available
 */
int sys_ipc_recv(void) {
    uint64_t sender_pid_ptr, w0_ptr, w1_ptr, w2_ptr;

    // Extract arguments (pointers to user space)
    if (arguint64(0, &sender_pid_ptr) < 0) return -1;
    if (arguint64(1, &w0_ptr) < 0) return -1;
    if (arguint64(2, &w1_ptr) < 0) return -1;
    if (arguint64(3, &w2_ptr) < 0) w2_ptr = 0;  // Optional

    struct proc *p = myproc();

    // Ensure we have a mailbox
    if (!p->mailbox) {
        return -1;
    }

    // Initialize mailbox if needed
    if (!p->mailbox->inited) {
        initlock(&p->mailbox->lock, "mailbox");
        p->mailbox->r = 0;
        p->mailbox->w = 0;
        p->mailbox->inited = 1;
    }

    // Block until message available
    acquire(&p->mailbox->lock);

    while (mailbox_is_empty(p->mailbox)) {
        // Check if we've been killed
        if (p->killed) {
            release(&p->mailbox->lock);
            return -1;
        }

        // Sleep on our mailbox (releases lock, reacquires on wake)
        ksleep(p->mailbox, &p->mailbox->lock);
    }

    // Dequeue message
    int sender_pid;
    uint64_t w0, w1, w2;

    if (mailbox_dequeue(p->mailbox, &sender_pid, &w0, &w1, &w2) < 0) {
        release(&p->mailbox->lock);
        return -1;  // Shouldn't happen, but safety check
    }

    release(&p->mailbox->lock);

    // Copy results to user space
    // Note: In a full implementation, we'd validate these pointers
    if (sender_pid_ptr) *(int *)sender_pid_ptr = sender_pid;
    if (w0_ptr) *(uint64_t *)w0_ptr = w0;
    if (w1_ptr) *(uint64_t *)w1_ptr = w1;
    if (w2_ptr) *(uint64_t *)w2_ptr = w2;

    return 0;
}

/**
 * Initialize a process's mailbox
 * Called from allocproc() or on first IPC use
 */
void mailbox_init(struct proc *p) {
    if (p->mailbox) {
        initlock(&p->mailbox->lock, "mailbox");
        p->mailbox->r = 0;
        p->mailbox->w = 0;
        p->mailbox->inited = 1;
    }
}

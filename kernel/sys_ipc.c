#include "types.h"
#include "defs.h"
#include "spinlock.h"
#include <stddef.h>

#ifndef TRACEPOINT
#define TRACEPOINT(x, ...)
#endif
#ifndef TRACE_IPC_DETAILS
#define TRACE_IPC_DETAILS(fmt, ...)
#endif
#ifndef TRACE_IPC_ERROR
#define TRACE_IPC_ERROR(fmt, ...)
#endif

// Basic thread identifiers and message tag structures.
typedef struct { uint32_t raw; } threadid_t;
typedef struct { uint32_t raw; } timeout_t;
typedef struct { uint32_t raw; } msg_tag_t;

// Simple thread control block used for the IPC syscall.
typedef struct tcb_t {
    struct spinlock lock;
    msg_tag_t tag;
    int state;
} tcb_t;

// Global TCB used by tests. Real kernels would look these up in a table.
tcb_t test_tcb;

static tcb_t *
tcb_get(threadid_t tid)
{
    // For now, only thread id 1 exists.
    return tid.raw == 1 ? &test_tcb : NULL;
}

static int
thread_is_nil(threadid_t tid)
{
    return tid.raw == 0;
}

int
sys_ipc(void)
{
    threadid_t to_tid;
    msg_tag_t tag;
    timeout_t timeout;

    if (argint(0, (int *)&to_tid.raw) < 0 ||
        argint(1, (int *)&tag.raw) < 0 ||
        argint(2, (int *)&timeout.raw) < 0)
        return -1;

    TRACEPOINT("sys_ipc_enter");
    TRACE_IPC_DETAILS("to=%u tag=%u", to_tid.raw, tag.raw);

    if (thread_is_nil(to_tid)) {
        TRACE_IPC_ERROR("nil destination");
        return -1;
    }

    tcb_t *dest = tcb_get(to_tid);
    if (dest == NULL) {
        TRACE_IPC_ERROR("invalid destination");
        return -1;
    }

    acquire(&dest->lock);
    dest->tag = tag;
    dest->state = 1; // Mark message queued
    release(&dest->lock);

    return 0;
}

/**
 * @file scheduler.c
 * @brief LibOS User-Space Thread Scheduler (Phase 6)
 *
 * This implements cooperative and preemptive multitasking entirely in user space.
 * The kernel only provides:
 *   - Timer IRQ upcalls (for preemption)
 *   - sys_yield() (for cooperative yields)
 *
 * The scheduler manages:
 *   - Thread creation/destruction
 *   - Round-robin scheduling
 *   - Context switching via thread_switch()
 */

#include <stdint.h>
#include <types.h>
#include <exov6_interface.h>

// Forward declarations
extern void print(const char *s);
extern void print_hex(uint64 n);
extern uint64 sys_alloc_page(void);
extern int sys_map_page(int target_env, uint64 phys, uint64 virt, int perm);

// Assembly context switch
extern void thread_switch(uint64 *old_sp, uint64 *new_sp);

// ═══════════════════════════════════════════════════════════════════════════
// Thread Control Block
// ═══════════════════════════════════════════════════════════════════════════

#define MAX_THREADS     32
#define THREAD_STACK_SIZE (4096 * 4)  // 16KB per thread

typedef enum {
    THREAD_FREE = 0,
    THREAD_READY,
    THREAD_RUNNING,
    THREAD_BLOCKED,
    THREAD_ZOMBIE
} thread_state_t;

typedef struct thread {
    int             tid;            // Thread ID
    thread_state_t  state;          // Current state
    uint64          sp;             // Saved stack pointer
    char           *stack_base;     // Base of allocated stack
    void          (*entry)(void*);  // Entry function
    void           *arg;            // Argument to entry function
    struct thread  *next;           // Next in run queue
    const char     *name;           // Debug name
} thread_t;

// ═══════════════════════════════════════════════════════════════════════════
// Scheduler State
// ═══════════════════════════════════════════════════════════════════════════

static thread_t thread_table[MAX_THREADS];
static thread_t *current_thread = 0;
static thread_t *run_queue_head = 0;
static thread_t *run_queue_tail = 0;
static int next_tid = 1;
static int scheduler_initialized = 0;

// Idle thread (runs when no other threads ready)
static thread_t idle_thread;
static char idle_stack[THREAD_STACK_SIZE] __attribute__((aligned(16)));

// ═══════════════════════════════════════════════════════════════════════════
// Run Queue Management
// ═══════════════════════════════════════════════════════════════════════════

static void
enqueue_thread(thread_t *t)
{
    t->next = 0;
    if (run_queue_tail) {
        run_queue_tail->next = t;
        run_queue_tail = t;
    } else {
        run_queue_head = run_queue_tail = t;
    }
}

static thread_t*
dequeue_thread(void)
{
    thread_t *t = run_queue_head;
    if (t) {
        run_queue_head = t->next;
        if (run_queue_head == 0)
            run_queue_tail = 0;
        t->next = 0;
    }
    return t;
}

// ═══════════════════════════════════════════════════════════════════════════
// Thread Entry Wrapper
// ═══════════════════════════════════════════════════════════════════════════

// Called when a thread returns from its entry function
static void
thread_exit_wrapper(void)
{
    print("LibOS: Thread ");
    print_hex(current_thread->tid);
    print(" exited\n");

    current_thread->state = THREAD_ZOMBIE;

    // Yield to let scheduler pick next thread
    extern void thread_yield(void);
    thread_yield();

    // Should never reach here
    for (;;) ;
}

// Trampoline to set up stack frame properly
static void
thread_trampoline(void)
{
    // Call the actual entry function
    current_thread->entry(current_thread->arg);

    // Thread returned - clean up
    thread_exit_wrapper();
}

// ═══════════════════════════════════════════════════════════════════════════
// Idle Thread
// ═══════════════════════════════════════════════════════════════════════════

static void
idle_thread_func(void *arg)
{
    (void)arg;
    for (;;) {
        // In a real system, we might halt here
        // For now, just spin and yield
        extern void sys_yield(void);
        sys_yield();
    }
}

// ═══════════════════════════════════════════════════════════════════════════
// Public API
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Initialize the scheduler
 * Must be called before creating any threads
 */
void
scheduler_init(void)
{
    if (scheduler_initialized)
        return;

    // Clear thread table
    for (int i = 0; i < MAX_THREADS; i++) {
        thread_table[i].tid = 0;
        thread_table[i].state = THREAD_FREE;
    }

    // Set up idle thread (doesn't go in thread_table)
    idle_thread.tid = 0;
    idle_thread.state = THREAD_READY;
    idle_thread.stack_base = idle_stack;
    idle_thread.entry = idle_thread_func;
    idle_thread.arg = 0;
    idle_thread.name = "idle";

    // Set up idle thread's initial stack
    uint64 sp = (uint64)(idle_stack + THREAD_STACK_SIZE);
    sp &= ~0xFULL;  // Align

    // Push fake return address and callee-saved registers
    // (matches what thread_switch expects)
#if defined(__x86_64__)
    sp -= 8; *(uint64*)sp = (uint64)thread_trampoline;  // Return address
    sp -= 8; *(uint64*)sp = 0;  // rbx
    sp -= 8; *(uint64*)sp = 0;  // rbp
    sp -= 8; *(uint64*)sp = 0;  // r12
    sp -= 8; *(uint64*)sp = 0;  // r13
    sp -= 8; *(uint64*)sp = 0;  // r14
    sp -= 8; *(uint64*)sp = 0;  // r15
#elif defined(__aarch64__)
    // ARM64: pairs of registers
    sp -= 16; // x19, x20
    sp -= 16; // x21, x22
    sp -= 16; // x23, x24
    sp -= 16; // x25, x26
    sp -= 16; // x27, x28
    sp -= 16; *(uint64*)(sp+8) = (uint64)thread_trampoline;  // x30 (lr)
#endif
    idle_thread.sp = sp;

    // Main thread becomes current (tid=1)
    // We'll create a thread_t for the main execution context
    thread_table[0].tid = next_tid++;
    thread_table[0].state = THREAD_RUNNING;
    thread_table[0].stack_base = 0;  // Main thread uses process stack
    thread_table[0].name = "main";
    current_thread = &thread_table[0];

    scheduler_initialized = 1;
    print("LibOS: Scheduler initialized\n");
}

/**
 * Create a new thread
 * @param entry Entry point function
 * @param arg Argument to pass to entry
 * @param name Debug name for thread
 * @return Thread ID, or -1 on failure
 */
int
thread_create(void (*entry)(void*), void *arg, const char *name)
{
    if (!scheduler_initialized)
        scheduler_init();

    // Find free slot
    thread_t *t = 0;
    for (int i = 0; i < MAX_THREADS; i++) {
        if (thread_table[i].state == THREAD_FREE) {
            t = &thread_table[i];
            break;
        }
    }
    if (!t) {
        print("LibOS: thread_create: no free slots\n");
        return -1;
    }

    // Allocate stack (TODO: use proper allocation)
    // For now, use a static pool
    static char thread_stacks[MAX_THREADS][THREAD_STACK_SIZE] __attribute__((aligned(16)));
    int slot = t - thread_table;
    t->stack_base = thread_stacks[slot];

    // Initialize thread
    t->tid = next_tid++;
    t->entry = entry;
    t->arg = arg;
    t->name = name ? name : "unnamed";

    // Set up initial stack (same as idle thread setup)
    uint64 sp = (uint64)(t->stack_base + THREAD_STACK_SIZE);
    sp &= ~0xFULL;

#if defined(__x86_64__)
    sp -= 8; *(uint64*)sp = (uint64)thread_trampoline;
    sp -= 8; *(uint64*)sp = 0;  // rbx
    sp -= 8; *(uint64*)sp = 0;  // rbp
    sp -= 8; *(uint64*)sp = 0;  // r12
    sp -= 8; *(uint64*)sp = 0;  // r13
    sp -= 8; *(uint64*)sp = 0;  // r14
    sp -= 8; *(uint64*)sp = 0;  // r15
#elif defined(__aarch64__)
    sp -= 16; // x19, x20
    sp -= 16; // x21, x22
    sp -= 16; // x23, x24
    sp -= 16; // x25, x26
    sp -= 16; // x27, x28
    sp -= 16; *(uint64*)(sp+8) = (uint64)thread_trampoline;  // lr
#endif
    t->sp = sp;

    // Mark ready and add to run queue
    t->state = THREAD_READY;
    enqueue_thread(t);

    print("LibOS: Created thread ");
    print_hex(t->tid);
    print(" '");
    print(t->name);
    print("'\n");

    return t->tid;
}

/**
 * Yield CPU to next ready thread (cooperative)
 */
void
thread_yield(void)
{
    if (!scheduler_initialized || !current_thread)
        return;

    // Get next thread from run queue
    thread_t *next = dequeue_thread();

    // If no threads ready, use idle thread
    if (!next) {
        next = &idle_thread;
    }

    // If same thread, nothing to do
    if (next == current_thread)
        return;

    // Put current thread back in queue if still runnable
    thread_t *old = current_thread;
    if (old->state == THREAD_RUNNING) {
        old->state = THREAD_READY;
        enqueue_thread(old);
    }

    // Switch to new thread
    next->state = THREAD_RUNNING;
    current_thread = next;

    // Perform context switch
    thread_switch(&old->sp, &next->sp);
}

/**
 * Called from timer IRQ upcall for preemptive scheduling
 */
void
thread_preempt(void)
{
    // Same as yield for now
    thread_yield();
}

/**
 * Get current thread ID
 */
int
thread_self(void)
{
    return current_thread ? current_thread->tid : 0;
}

/**
 * Get current thread name
 */
const char*
thread_name(void)
{
    return current_thread ? current_thread->name : "(none)";
}

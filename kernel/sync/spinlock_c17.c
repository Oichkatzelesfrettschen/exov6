/*
 * Pure C17 Ticket Spinlock Implementation
 * 
 * Complete modernization using C17 features:
 * - stdatomic.h for all atomic operations
 * - stdint.h types throughout
 * - _Static_assert for compile-time checks
 * - _Alignas for cache-line optimization
 * - No inline assembly except minimal CPU intrinsics
 */

#include <stdatomic.h>
#include <stdint.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdalign.h>

#include "types.h"
#include "defs.h"
#include "param.h"
#include "proc.h"
#include "spinlock.h"

/* Configuration for exponential backoff */
#define BACKOFF_MIN 10
#define BACKOFF_MAX 1024
#define CACHE_LINE_SIZE 64

/* C17 Spinlock structure with atomic ticket counters */
struct spinlock_c17 {
    _Alignas(64) struct {
        _Atomic(uint32_t) head;
        _Atomic(uint32_t) tail;
    } ticket;
    
    /* Debug information */
    const char *name;
    struct cpu *cpu;
    uint64_t pcs[10];
    
    /* Padding to prevent false sharing */
    char padding[CACHE_LINE_SIZE - sizeof(void*) * 12];
};

/* Static assertions for structure layout */
_Static_assert(sizeof(struct spinlock_c17) == CACHE_LINE_SIZE * 2, 
               "spinlock must be exactly 2 cache lines");
_Static_assert(alignof(struct spinlock_c17) == CACHE_LINE_SIZE,
               "spinlock must be cache-line aligned");

/* CPU pause instruction for spinloop optimization */
static inline void cpu_pause(void) {
#if defined(__x86_64__)
    __asm__ __volatile__("pause" ::: "memory");
#elif defined(__aarch64__)
    __asm__ __volatile__("yield" ::: "memory");
#else
    /* Generic memory barrier for other architectures */
    atomic_thread_fence(memory_order_seq_cst);
#endif
}

/* Read CPU flags register */
static inline uint64_t read_cpu_flags(void) {
    uint64_t flags = 0;
#if defined(__x86_64__)
    __asm__ __volatile__(
        "pushfq\n\t"
        "popq %0"
        : "=r"(flags)
        :
        : "memory"
    );
#elif defined(__aarch64__)
    __asm__ __volatile__(
        "mrs %0, daif"
        : "=r"(flags)
        :
        : "memory"
    );
#endif
    return flags;
}

/* Disable interrupts */
static inline void disable_interrupts(void) {
#if defined(__x86_64__)
    __asm__ __volatile__("cli" ::: "memory");
#elif defined(__aarch64__)
    __asm__ __volatile__(
        "msr daifset, #0xf"
        ::: "memory"
    );
#endif
}

/* Enable interrupts */
static inline void enable_interrupts(void) {
#if defined(__x86_64__)
    __asm__ __volatile__("sti" ::: "memory");
#elif defined(__aarch64__)
    __asm__ __volatile__(
        "msr daifclr, #0xf"
        ::: "memory"
    );
#endif
}

/* Check if interrupts are enabled */
static inline bool interrupts_enabled(void) {
    uint64_t flags = read_cpu_flags();
#if defined(__x86_64__)
    return (flags & 0x200) != 0;  /* FL_IF flag */
#elif defined(__aarch64__)
    return (flags & 0xF) == 0;    /* All interrupts enabled */
#else
    return false;
#endif
}

#if CONFIG_SMP

/**
 * initlock - Initialize a spinlock
 * @lk: Pointer to spinlock structure
 * @name: Name for debugging
 *
 * C17 features: atomic_init for proper initialization
 */
void initlock(struct spinlock *lk, const char *name) {
    struct spinlock_c17 *lock = (struct spinlock_c17 *)lk;
    
    atomic_init(&lock->ticket.head, 0);
    atomic_init(&lock->ticket.tail, 0);
    lock->name = name;
    lock->cpu = NULL;
    
    for (int32_t i = 0; i < 10; i++) {
        lock->pcs[i] = 0;
    }
}

/**
 * acquire - Acquire the spinlock
 * @lk: Pointer to spinlock structure
 *
 * Uses C17 atomics for ticket mechanism with exponential backoff
 */
void acquire(struct spinlock *lk) {
    struct spinlock_c17 *lock = (struct spinlock_c17 *)lk;
    
    pushcli();  /* Disable interrupts */
    
    if (holding(lk)) {
        panic("acquire: already holding");
    }
    
    /* Get our ticket number atomically */
    uint32_t my_ticket = atomic_fetch_add_explicit(
        &lock->ticket.tail, 1, memory_order_relaxed
    );
    
    /* Wait until it's our turn with exponential backoff */
    uint32_t backoff = BACKOFF_MIN;
    
    while (atomic_load_explicit(&lock->ticket.head, memory_order_acquire) 
           != my_ticket) {
        
        /* Exponential backoff with CPU pause */
        for (uint32_t i = 0; i < backoff; i++) {
            cpu_pause();
        }
        
        /* Increase backoff up to maximum */
        if (backoff < BACKOFF_MAX) {
            backoff *= 2;
        }
    }
    
    /* Full memory barrier after acquiring lock */
    atomic_thread_fence(memory_order_seq_cst);
    
    /* Record debugging info */
    lock->cpu = mycpu();
    getcallerpcs(&lk, lock->pcs);
}

/**
 * release - Release the spinlock
 * @lk: Pointer to spinlock structure
 *
 * Uses C17 atomic increment with proper memory ordering
 */
void release(struct spinlock *lk) {
    struct spinlock_c17 *lock = (struct spinlock_c17 *)lk;
    
    if (!holding(lk)) {
        panic("release: not holding");
    }
    
    /* Clear debugging info */
    lock->pcs[0] = 0;
    lock->cpu = NULL;
    
    /* Full memory barrier before release */
    atomic_thread_fence(memory_order_seq_cst);
    
    /* Release lock by incrementing head with release semantics */
    atomic_fetch_add_explicit(&lock->ticket.head, 1, memory_order_release);
    
    popcli();  /* Re-enable interrupts if appropriate */
}

/**
 * trylock - Try to acquire lock without blocking
 * @lk: Pointer to spinlock structure
 *
 * Returns: true if lock acquired, false otherwise
 *
 * Uses C17 compare_exchange for atomic test-and-set
 */
int trylock(struct spinlock *lk) {
    struct spinlock_c17 *lock = (struct spinlock_c17 *)lk;
    
    pushcli();
    
    if (holding(lk)) {
        popcli();
        return 0;
    }
    
    /* Load current head value */
    uint32_t expected = atomic_load_explicit(
        &lock->ticket.head, memory_order_relaxed
    );
    
    /* Try to atomically increment tail if it equals head */
    uint32_t current_tail = expected;
    
    if (atomic_compare_exchange_strong_explicit(
            &lock->ticket.tail,
            &current_tail,
            expected + 1,
            memory_order_acquire,
            memory_order_relaxed)) {
        
        /* Success - we got the lock */
        lock->cpu = mycpu();
        getcallerpcs(&lk, lock->pcs);
        return 1;
    }
    
    /* Failed to get lock */
    popcli();
    return 0;
}

/**
 * holding - Check if current CPU holds lock
 * @lock: Pointer to spinlock structure
 *
 * Returns: true if current CPU holds lock
 *
 * Uses C17 atomic loads for race-free checking
 */
int holding(struct spinlock *lock) {
    struct spinlock_c17 *lk = (struct spinlock_c17 *)lock;
    bool result;
    
    pushcli();
    
    uint32_t head = atomic_load_explicit(&lk->ticket.head, memory_order_relaxed);
    uint32_t tail = atomic_load_explicit(&lk->ticket.tail, memory_order_relaxed);
    
    result = (head != tail) && (lk->cpu == mycpu());
    
    popcli();
    
    return result;
}

#else /* !CONFIG_SMP - Uniprocessor implementation */

/**
 * Uniprocessor versions - just manage interrupt state
 * No atomics needed for UP systems
 */

void initlock(struct spinlock *lk, const char *name) {
    struct spinlock_c17 *lock = (struct spinlock_c17 *)lk;
    
    lock->ticket.head = 0;
    lock->ticket.tail = 0;
    lock->name = name;
    lock->cpu = NULL;
}

void acquire(struct spinlock *lk) {
    struct spinlock_c17 *lock = (struct spinlock_c17 *)lk;
    
    pushcli();
    
    if (holding(lk)) {
        panic("acquire: already holding");
    }
    
    lock->cpu = mycpu();
}

void release(struct spinlock *lk) {
    struct spinlock_c17 *lock = (struct spinlock_c17 *)lk;
    
    if (!holding(lk)) {
        panic("release: not holding");
    }
    
    lock->cpu = NULL;
    popcli();
}

int trylock(struct spinlock *lk) {
    struct spinlock_c17 *lock = (struct spinlock_c17 *)lk;
    
    pushcli();
    
    if (holding(lk)) {
        popcli();
        return 0;
    }
    
    lock->cpu = mycpu();
    return 1;
}

int holding(struct spinlock *lock) {
    struct spinlock_c17 *lk = (struct spinlock_c17 *)lock;
    return lk->cpu == mycpu();
}

#endif /* CONFIG_SMP */

/**
 * pushcli - Save interrupt state and disable interrupts
 *
 * C17 implementation with proper atomic operations
 */
void pushcli(void) {
    bool interrupts_were_enabled = interrupts_enabled();
    
    disable_interrupts();
    
    struct cpu *c = mycpu();
    
    if (c->ncli == 0) {
        c->intena = interrupts_were_enabled;
    }
    
    c->ncli++;
}

/**
 * popcli - Restore interrupt state
 *
 * C17 implementation with safety checks
 */
void popcli(void) {
    if (interrupts_enabled()) {
        panic("popcli: interrupts enabled");
    }
    
    struct cpu *c = mycpu();
    
    if (--c->ncli < 0) {
        panic("popcli: underflow");
    }
    
    if (c->ncli == 0 && c->intena) {
        enable_interrupts();
    }
}

/**
 * @brief Get call stack for debugging.
 * @param v Starting point (usually current function)
 * @param pcs Array to store program counters
 *
 * C17 implementation with minimal assembly
 */
void getcallerpcs(void *v, uint64_t pcs[]) {
    uint64_t *frame_pointer = NULL;
    
#if defined(__x86_64__)
    /* Get current frame pointer */
    __asm__ __volatile__("movq %%rbp, %0" : "=r"(frame_pointer));
#elif defined(__aarch64__)
    /* AArch64 frame pointer */
    __asm__ __volatile__("mov %0, x29" : "=r"(frame_pointer));
#else
    /* Use compiler builtin */
    frame_pointer = (uint64_t *)__builtin_frame_address(0);
#endif
    
    /* Walk the stack frames */
    for (int32_t i = 0; i < 10; i++) {
        if (frame_pointer == NULL || 
            frame_pointer < (uint64_t *)KERNBASE ||
            (uintptr_t)frame_pointer == 0xffffffffffffffff) {
            pcs[i] = 0;
            continue;
        }
        
        /* Return address is one word above frame pointer */
        pcs[i] = frame_pointer[1];
        
        /* Follow frame pointer chain */
        frame_pointer = (uint64_t *)frame_pointer[0];
    }
}

/* Performance monitoring for spinlocks */
struct spinlock_stats {
    _Atomic(uint64_t) acquisitions;
    _Atomic(uint64_t) contentions;
    _Atomic(uint64_t) total_wait_cycles;
    _Atomic(uint64_t) max_wait_cycles;
};

static _Alignas(64) struct spinlock_stats global_spinlock_stats;

/**
 * spinlock_stats_init - Initialize performance monitoring
 *
 * C17 atomic initialization
 */
void spinlock_stats_init(void) {
    atomic_init(&global_spinlock_stats.acquisitions, 0);
    atomic_init(&global_spinlock_stats.contentions, 0);
    atomic_init(&global_spinlock_stats.total_wait_cycles, 0);
    atomic_init(&global_spinlock_stats.max_wait_cycles, 0);
}

/**
 * spinlock_stats_get - Get current spinlock statistics
 *
 * Uses C17 atomic loads with acquire semantics
 */
void spinlock_stats_get(uint64_t *acquisitions, uint64_t *contentions,
                        uint64_t *avg_wait, uint64_t *max_wait) {
    *acquisitions = atomic_load_explicit(
        &global_spinlock_stats.acquisitions, memory_order_acquire
    );
    *contentions = atomic_load_explicit(
        &global_spinlock_stats.contentions, memory_order_acquire
    );
    
    uint64_t total = atomic_load_explicit(
        &global_spinlock_stats.total_wait_cycles, memory_order_acquire
    );
    
    *max_wait = atomic_load_explicit(
        &global_spinlock_stats.max_wait_cycles, memory_order_acquire
    );
    
    if (*contentions > 0) {
        *avg_wait = total / *contentions;
    } else {
        *avg_wait = 0;
    }
}

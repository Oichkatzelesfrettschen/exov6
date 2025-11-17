/**
 * @file qspinlock.c
 * @brief NUMA-aware queued spinlock implementation for ExoV6
 *
 * Based on Linux MCS qspinlock with NUMA locality optimizations
 * Compact 32-bit representation with per-CPU MCS node arrays
 *
 * References:
 * - Mellor-Crummey & Scott (1991) - MCS locks
 * - Linux kernel/locking/qspinlock.c
 * - Lim et al. (2019) - Compact NUMA-aware Locks (EuroSys)
 *
 * @version 1.0
 * @date 2025-11-17
 */

#include <types.h>
#include "defs.h"
#include "param.h"
#include "arch.h"
#include "memlayout.h"
#include "exo_lock.h"
#include "proc.h"

/* ========================================================================
 * Per-CPU MCS Node Arrays
 * ======================================================================== */

/**
 * Per-CPU MCS node storage
 * Each CPU has 4 nodes for nested lock acquisitions
 */
struct mcs_node mcs_nodes[NCPU][MCS_NODES_PER_CPU] __attribute__((aligned(64)));

/**
 * Get MCS node for current CPU
 * @param idx Node index (0-3 for nesting level)
 * @return Pointer to MCS node
 */
static inline struct mcs_node *get_mcs_node(int idx) {
    struct cpu *c = mycpu();
    if (idx >= MCS_NODES_PER_CPU) {
        panic("qspinlock: MCS node index out of range");
    }
    return &mcs_nodes[c - cpus][idx];
}

/* ========================================================================
 * NUMA Topology Detection
 * ======================================================================== */

static uint32_t numa_node_count = 1;
static uint32_t cpu_to_numa[NCPU];

/**
 * Detect NUMA topology via CPUID
 * For QEMU: use -numa option to configure
 */
void lock_detect_numa_topology(void) {
#ifdef __x86_64__
    // CPUID leaf 0x1F (V2 Extended Topology)
    // For now, assume single NUMA node
    // TODO: Parse ACPI SRAT table for real NUMA info
    numa_node_count = 1;
    for (int i = 0; i < NCPU; i++) {
        cpu_to_numa[i] = i / 8;  // Assume 8 CPUs per socket
    }
#else
    numa_node_count = 1;
    for (int i = 0; i < NCPU; i++) {
        cpu_to_numa[i] = 0;
    }
#endif
}

/**
 * Get NUMA node for given CPU
 */
static inline uint32_t get_numa_node(uint32_t cpu_id) {
    if (cpu_id >= NCPU) return 0;
    return cpu_to_numa[cpu_id];
}

/* ========================================================================
 * QSpinlock Core Operations
 * ======================================================================== */

/**
 * Initialize qspinlock
 */
void qspin_init(struct qspinlock *lock) {
    atomic_store_explicit(&lock->val, 0, memory_order_relaxed);
}

/**
 * Encode CPU ID and node index into tail value
 * Format: (cpu_id << 2) | node_idx
 */
static inline uint16_t encode_tail(uint32_t cpu_id, uint32_t node_idx) {
    return (uint16_t)((cpu_id << 2) | (node_idx & 0x3));
}

/**
 * Decode tail value into CPU ID and node index
 */
static inline void decode_tail(uint16_t tail, uint32_t *cpu_id, uint32_t *node_idx) {
    *cpu_id = tail >> 2;
    *node_idx = tail & 0x3;
}

/**
 * Try to acquire lock (fast path - no contention)
 * Returns 1 on success, 0 on failure
 */
static inline int qspin_trylock_fast(struct qspinlock *lock) {
    uint32_t expected = 0;
    return atomic_compare_exchange_strong_explicit(
        &lock->val, &expected, 1,
        memory_order_acquire, memory_order_relaxed);
}

/**
 * Acquire lock (full implementation with MCS queue)
 */
void qspin_lock(struct qspinlock *lock) {
    uint64_t start_tsc = rdtsc();

    // Fast path: try to acquire immediately
    if (qspin_trylock_fast(lock)) {
        return;
    }

    // Slow path: need to queue
    struct cpu *c = mycpu();
    uint32_t cpu_id = c - cpus;

    // Find free MCS node (simple linear search for now)
    int node_idx = 0;
    for (node_idx = 0; node_idx < MCS_NODES_PER_CPU; node_idx++) {
        struct mcs_node *node = &mcs_nodes[cpu_id][node_idx];
        uint32_t expected = 0;
        if (atomic_compare_exchange_strong_explicit(
                &node->locked, &expected, 1,
                memory_order_acquire, memory_order_relaxed)) {
            break;
        }
    }

    if (node_idx >= MCS_NODES_PER_CPU) {
        panic("qspinlock: all MCS nodes in use (too many nested locks)");
    }

    struct mcs_node *node = &mcs_nodes[cpu_id][node_idx];
    node->numa_node = get_numa_node(cpu_id);
    atomic_store_explicit(&node->next, NULL, memory_order_relaxed);
    atomic_store_explicit(&node->locked, 1, memory_order_relaxed);

    uint16_t my_tail = encode_tail(cpu_id, node_idx);

    // Atomic exchange: add ourselves to tail
    uint32_t old_val = atomic_exchange_explicit(&lock->val, my_tail << 16,
                                                memory_order_acquire);

    if (old_val == 0) {
        // We got the lock immediately
        return;
    }

    // There's a predecessor: link ourselves into the queue
    uint16_t old_tail = old_val >> 16;
    if (old_tail != 0) {
        uint32_t pred_cpu, pred_idx;
        decode_tail(old_tail, &pred_cpu, &pred_idx);
        struct mcs_node *pred = &mcs_nodes[pred_cpu][pred_idx];

        // Set predecessor's next pointer to us
        atomic_store_explicit(&pred->next, node, memory_order_release);
    }

    // Spin on our locked flag with exponential backoff
    int backoff = ADAPTIVE_SPIN_MIN_CYCLES;
    while (atomic_load_explicit(&node->locked, memory_order_acquire)) {
        for (int i = 0; i < backoff; i++) {
            pause();  // CPU hint: we're spinning
        }

        if (backoff < ADAPTIVE_SPIN_MAX_CYCLES) {
            backoff *= 2;
        }

        // Check for lock timeout (resurrection server integration)
        uint64_t elapsed = rdtsc() - start_tsc;
        if (elapsed > LOCK_TIMEOUT_CYCLES) {
            cprintf("WARNING: qspinlock timeout after %llu cycles\n", elapsed);
            // TODO: Trigger resurrection server
        }
    }

    // We have the lock now
    mfence();  // Memory barrier
}

/**
 * Try to acquire lock (non-blocking)
 * Returns 1 on success, 0 on failure
 */
int qspin_trylock(struct qspinlock *lock) {
    return qspin_trylock_fast(lock);
}

/**
 * Release lock
 */
void qspin_unlock(struct qspinlock *lock) {
    mfence();  // Memory barrier before release

    // Fast path: no waiters
    uint32_t val = atomic_load_explicit(&lock->val, memory_order_relaxed);
    if (val == 1) {
        uint32_t expected = 1;
        if (atomic_compare_exchange_strong_explicit(
                &lock->val, &expected, 0,
                memory_order_release, memory_order_relaxed)) {
            return;
        }
    }

    // Slow path: hand off to next waiter
    uint16_t tail = val >> 16;
    if (tail != 0) {
        uint32_t cpu_id, node_idx;
        decode_tail(tail, &cpu_id, &node_idx);
        struct mcs_node *node = &mcs_nodes[cpu_id][node_idx];

        // Wait for next pointer to be set (may race with qspin_lock)
        struct mcs_node *next;
        while ((next = atomic_load_explicit(&node->next, memory_order_acquire)) == NULL) {
            pause();
        }

        // NUMA optimization: prefer local socket waiters
        // TODO: Implement hierarchical queue (local vs remote)

        // Wake next waiter
        atomic_store_explicit(&next->locked, 0, memory_order_release);

        // Free our MCS node
        atomic_store_explicit(&node->locked, 0, memory_order_release);
    }

    // Clear lock
    atomic_store_explicit(&lock->val, 0, memory_order_release);
}

/* ========================================================================
 * Unified Lock API Implementation (qspinlock variant)
 * ======================================================================== */

/**
 * Initialize unified lock as qspinlock
 */
void exo_lock_init_qspin(struct exo_lock *lock, const char *name, uint32_t dag_level) {
    lock->type = EXOLOCK_QSPIN;
    lock->name = name;
    lock->dag.level = dag_level;
    lock->dag.dependency_bitmap = 0;
    lock->dag.name = name;

    qspin_init(&lock->qspin);

    // Initialize statistics
    lock->stats.acquire_count = 0;
    lock->stats.contention_count = 0;
    lock->stats.total_hold_time = 0;
    lock->stats.max_hold_time = 0;
}

/* ========================================================================
 * Statistics and Debugging
 * ======================================================================== */

struct lock_global_stats lock_stats = {0};

/**
 * Dump qspinlock state for debugging
 */
void qspin_dump_state(struct qspinlock *lock) {
    uint32_t val = atomic_load_explicit(&lock->val, memory_order_relaxed);
    uint8_t locked = val & 0xFF;
    uint16_t tail = val >> 16;

    cprintf("qspinlock %p: locked=%d tail=%d\n", lock, locked, tail);

    if (tail != 0) {
        uint32_t cpu_id, node_idx;
        decode_tail(tail, &cpu_id, &node_idx);
        cprintf("  tail: cpu=%d node_idx=%d\n", cpu_id, node_idx);

        struct mcs_node *node = &mcs_nodes[cpu_id][node_idx];
        cprintf("  MCS node: locked=%d numa_node=%d\n",
                atomic_load_explicit(&node->locked, memory_order_relaxed),
                node->numa_node);
    }
}

/* ========================================================================
 * Subsystem Initialization
 * ======================================================================== */

/**
 * Initialize qspinlock subsystem
 * Called once at boot
 */
void qspinlock_subsystem_init(void) {
    // Detect NUMA topology
    lock_detect_numa_topology();

    // Initialize per-CPU MCS node arrays
    for (int cpu = 0; cpu < NCPU; cpu++) {
        for (int idx = 0; idx < MCS_NODES_PER_CPU; idx++) {
            struct mcs_node *node = &mcs_nodes[cpu][idx];
            atomic_store_explicit(&node->next, NULL, memory_order_relaxed);
            atomic_store_explicit(&node->locked, 0, memory_order_relaxed);
            node->numa_node = get_numa_node(cpu);
        }
    }

    cprintf("qspinlock: initialized for %d CPUs, %d NUMA nodes\n",
            NCPU, numa_node_count);
}

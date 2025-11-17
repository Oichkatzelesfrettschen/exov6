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
#include "compiler_attrs.h"
#include "exo_lock.h"
#include "proc.h"

/* ========================================================================
 * Architecture-Specific Helpers
 * ======================================================================== */

/**
 * Read Time-Stamp Counter (non-serialized)
 * For lock timing, we don't need full serialization - just cycle counting
 */
static inline uint64_t rdtsc(void) {
    uint32_t lo, hi;
    __asm__ __volatile__("rdtsc" : "=a"(lo), "=d"(hi));
    return ((uint64_t)hi << 32) | lo;
}

/**
 * Memory fence (full barrier)
 */
static inline void mfence(void) {
    __asm__ __volatile__("mfence" ::: "memory");
}

/**
 * CPU pause hint (for spin loops)
 */
static inline void pause(void) {
    __asm__ __volatile__("pause" ::: "memory");
}

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
static EXO_ALWAYS_INLINE struct mcs_node *get_mcs_node(int idx) {
    struct cpu *c = mycpu();
    if (unlikely(idx >= MCS_NODES_PER_CPU)) {
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
 * CPUID wrapper for topology detection
 */
static inline void cpuid_topology(uint32_t leaf, uint32_t subleaf,
                                  uint32_t *eax, uint32_t *ebx,
                                  uint32_t *ecx, uint32_t *edx) {
#ifdef __x86_64__
    __asm__ volatile("cpuid"
                     : "=a"(*eax), "=b"(*ebx), "=c"(*ecx), "=d"(*edx)
                     : "a"(leaf), "c"(subleaf));
#else
    *eax = *ebx = *ecx = *edx = 0;
#endif
}

/**
 * Detect NUMA topology via CPUID Extended Topology
 * Uses CPUID leaf 0x1F (V2 Extended Topology) or 0x0B (Extended Topology)
 */
static int detect_numa_via_cpuid(void) {
#ifdef __x86_64__
    uint32_t eax, ebx, ecx, edx;

    // Check if extended topology is supported
    cpuid_topology(0, 0, &eax, &ebx, &ecx, &edx);
    if (eax < 0x0B) {
        return -1;  // Extended topology not supported
    }

    // Try CPUID leaf 0x1F first (V2 Extended Topology)
    uint32_t leaf = 0x1F;
    cpuid_topology(leaf, 0, &eax, &ebx, &ecx, &edx);

    // If 0x1F not supported, fall back to 0x0B
    if (ebx == 0) {
        leaf = 0x0B;
    }

    // Enumerate topology levels
    int socket_shift = 0;
    for (uint32_t subleaf = 0; subleaf < 8; subleaf++) {
        cpuid_topology(leaf, subleaf, &eax, &ebx, &ecx, &edx);

        if (ebx == 0) {
            break;  // No more levels
        }

        uint32_t level_type = (ecx >> 8) & 0xFF;
        uint32_t shift = eax & 0x1F;

        // Level types: 1 = SMT, 2 = Core, 3 = Module, 5 = Die (socket)
        if (level_type == 2) {
            // Core level - use this for NUMA if no socket level
            socket_shift = shift;
        } else if (level_type == 5) {
            // Socket/Die level - best indicator of NUMA
            socket_shift = shift;
            break;
        }
    }

    if (socket_shift > 0) {
        // Map CPUs to NUMA nodes based on socket shift
        uint32_t socket_mask = (1U << socket_shift) - 1;

        for (int i = 0; i < NCPU; i++) {
            // APIC ID >> socket_shift = socket ID = NUMA node
            // For now, assume APIC ID == CPU ID
            cpu_to_numa[i] = i >> socket_shift;
        }

        // Count unique NUMA nodes
        numa_node_count = (NCPU + socket_mask) >> socket_shift;
        if (numa_node_count > 64) numa_node_count = 1;  // Sanity check

        return 0;  // Success
    }
#endif

    return -1;  // Failed to detect
}

/**
 * Heuristic NUMA detection for QEMU
 * Assumes 8 CPUs per socket (common QEMU configuration)
 */
static void detect_numa_heuristic(void) {
    // QEMU default: 8 CPUs per socket
    // This works for: -smp 16,sockets=2,cores=4,threads=2
    const int cpus_per_socket = 8;

    for (int i = 0; i < NCPU; i++) {
        cpu_to_numa[i] = i / cpus_per_socket;
    }

    numa_node_count = (NCPU + cpus_per_socket - 1) / cpus_per_socket;
    if (numa_node_count == 0) numa_node_count = 1;
}

/**
 * Parse ACPI SRAT (System Resource Affinity Table) for NUMA info
 * TODO: Implement full ACPI table parsing
 */
static int detect_numa_via_acpi_srat(void) {
    // Placeholder for future ACPI SRAT parsing
    // Would read from ACPI tables at physical address
    // and extract processor affinity and memory affinity structures
    return -1;  // Not implemented yet
}

/**
 * Detect NUMA topology with fallbacks
 * Tries: 1) ACPI SRAT, 2) CPUID, 3) Heuristic
 */
void lock_detect_numa_topology(void) {
    // Try ACPI SRAT first (most accurate)
    if (detect_numa_via_acpi_srat() == 0) {
        cprintf("qspinlock: NUMA topology via ACPI SRAT: %d nodes\n",
                numa_node_count);
        return;
    }

    // Try CPUID Extended Topology
    if (detect_numa_via_cpuid() == 0) {
        cprintf("qspinlock: NUMA topology via CPUID: %d nodes\n",
                numa_node_count);
        return;
    }

    // Fallback: heuristic (assume 8 CPUs per socket)
    detect_numa_heuristic();
    cprintf("qspinlock: NUMA topology via heuristic: %d nodes (8 CPUs/socket)\n",
            numa_node_count);
}

/**
 * Get NUMA node for given CPU
 */
static EXO_ALWAYS_INLINE uint32_t get_numa_node(uint32_t cpu_id) {
    if (unlikely(cpu_id >= NCPU)) return 0;
    return cpu_to_numa[cpu_id];
}

/**
 * Export NUMA info for other subsystems
 */
uint32_t lock_get_numa_node_count(void) {
    return numa_node_count;
}

uint32_t lock_get_cpu_numa_node(uint32_t cpu_id) {
    return get_numa_node(cpu_id);
}

/* ========================================================================
 * QSpinlock Core Operations
 * ======================================================================== */

/**
 * Initialize qspinlock
 */
void qspin_init(struct qspinlock *lock) {
    atomic_store_explicit(&lock->val, 0, memory_order_relaxed);

    // Initialize statistics
    lock->stats.fast_path_count = 0;
    lock->stats.slow_path_count = 0;
    lock->stats.local_handoff_count = 0;
    lock->stats.remote_handoff_count = 0;
    lock->stats.total_spin_cycles = 0;
    lock->stats.max_spin_cycles = 0;
    lock->stats.max_queue_depth = 0;
    lock->stats.total_hold_cycles = 0;
    lock->stats.max_hold_cycles = 0;
    lock->stats.acquire_count = 0;

    lock->last_acquire_tsc = 0;
    lock->last_owner_numa = 0;
}

/**
 * Encode CPU ID and node index into tail value
 * Format: (cpu_id << 2) | node_idx
 */
static EXO_ALWAYS_INLINE uint16_t encode_tail(uint32_t cpu_id, uint32_t node_idx) {
    return (uint16_t)((cpu_id << 2) | (node_idx & 0x3));
}

/**
 * Decode tail value into CPU ID and node index
 */
static EXO_ALWAYS_INLINE void decode_tail(uint16_t tail, uint32_t *cpu_id, uint32_t *node_idx) {
    *cpu_id = tail >> 2;
    *node_idx = tail & 0x3;
}

/**
 * Try to acquire lock (fast path - no contention)
 * Returns 1 on success, 0 on failure
 *
 * OPTIMIZATION: Force inline to minimize overhead on uncontended path
 */
static EXO_ALWAYS_INLINE int qspin_trylock_fast(struct qspinlock *lock) {
    uint32_t expected = 0;
    if (likely(atomic_compare_exchange_strong_explicit(
            &lock->val, &expected, 1,
            memory_order_acquire, memory_order_relaxed))) {
        // Fast path success - record statistics
        __sync_fetch_and_add(&lock->stats.fast_path_count, 1);
        __sync_fetch_and_add(&lock->stats.acquire_count, 1);

        lock->last_acquire_tsc = rdtsc();
        lock->last_owner_numa = get_numa_node(mycpu() - cpus);

        return 1;
    }
    return 0;
}

/**
 * Acquire lock (full implementation with MCS queue)
 */
void qspin_lock(struct qspinlock *lock) {
    uint64_t start_tsc = rdtsc();

    // Fast path: try to acquire immediately (LIKELY: most locks are uncontended)
    if (likely(qspin_trylock_fast(lock))) {
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

    if (unlikely(node_idx >= MCS_NODES_PER_CPU)) {
        panic("qspinlock: all MCS nodes in use (too many nested locks)");
    }

    struct mcs_node *node = &mcs_nodes[cpu_id][node_idx];
    uint32_t my_numa = get_numa_node(cpu_id);
    node->numa_node = my_numa;
    atomic_store_explicit(&node->next, NULL, memory_order_relaxed);
    atomic_store_explicit(&node->local_next, NULL, memory_order_relaxed);
    atomic_store_explicit(&node->locked, 1, memory_order_relaxed);
    node->is_local = 0;

    uint16_t my_tail = encode_tail(cpu_id, node_idx);

    // Atomic exchange: add ourselves to tail
    uint32_t old_val = atomic_exchange_explicit(&lock->val, my_tail << 16,
                                                memory_order_acquire);

    if (unlikely(old_val == 0)) {
        // We got the lock immediately (unlikely since fast path failed)
        return;
    }

    // There's a predecessor: link ourselves into the queue
    uint16_t old_tail = old_val >> 16;
    if (likely(old_tail != 0)) {
        uint32_t pred_cpu, pred_idx;
        decode_tail(old_tail, &pred_cpu, &pred_idx);
        struct mcs_node *pred = &mcs_nodes[pred_cpu][pred_idx];

        // Set predecessor's global next pointer to us
        atomic_store_explicit(&pred->next, node, memory_order_release);

        // HIERARCHICAL QUEUE: Link into local queue if same NUMA node
        if (likely(pred->numa_node == my_numa)) {
            node->is_local = 1;
            atomic_store_explicit(&pred->local_next, node, memory_order_release);
        }
    }

    // Record slow path
    __sync_fetch_and_add(&lock->stats.slow_path_count, 1);
    __sync_fetch_and_add(&lock->stats.acquire_count, 1);

    // Spin on our locked flag with exponential backoff
    uint64_t spin_start = rdtsc();
    int backoff = ADAPTIVE_SPIN_MIN_CYCLES;
    while (atomic_load_explicit(&node->locked, memory_order_acquire)) {
        for (int i = 0; i < backoff; i++) {
            pause();  // CPU hint: we're spinning
        }

        if (likely(backoff < ADAPTIVE_SPIN_MAX_CYCLES)) {
            backoff *= 2;
        }

        // Check for lock timeout (resurrection server integration)
        uint64_t elapsed = rdtsc() - start_tsc;
        if (unlikely(elapsed > LOCK_TIMEOUT_CYCLES)) {
            cprintf("WARNING: qspinlock timeout after %llu cycles\n", elapsed);
            // TODO: Trigger resurrection server
        }
    }

    // Record spin time
    uint64_t spin_cycles = rdtsc() - spin_start;
    __sync_fetch_and_add(&lock->stats.total_spin_cycles, spin_cycles);

    // Update max spin time (atomic max)
    uint64_t old_max = lock->stats.max_spin_cycles;
    while (spin_cycles > old_max) {
        if (__sync_bool_compare_and_swap(&lock->stats.max_spin_cycles,
                                         old_max, spin_cycles)) {
            break;
        }
        old_max = lock->stats.max_spin_cycles;
    }

    // We have the lock now
    lock->last_acquire_tsc = rdtsc();
    lock->last_owner_numa = my_numa;

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
    // Track hold time
    uint64_t hold_cycles = rdtsc() - lock->last_acquire_tsc;
    __sync_fetch_and_add(&lock->stats.total_hold_cycles, hold_cycles);

    // Update max hold time
    uint64_t old_max = lock->stats.max_hold_cycles;
    while (hold_cycles > old_max) {
        if (__sync_bool_compare_and_swap(&lock->stats.max_hold_cycles,
                                         old_max, hold_cycles)) {
            break;
        }
        old_max = lock->stats.max_hold_cycles;
    }

    mfence();  // Memory barrier before release

    // Fast path: no waiters (LIKELY: most releases are uncontended)
    uint32_t val = atomic_load_explicit(&lock->val, memory_order_relaxed);
    if (likely(val == 1)) {
        uint32_t expected = 1;
        if (likely(atomic_compare_exchange_strong_explicit(
                &lock->val, &expected, 0,
                memory_order_release, memory_order_relaxed))) {
            return;
        }
    }

    // Slow path: hand off to next waiter
    uint16_t tail = val >> 16;
    if (likely(tail != 0)) {
        uint32_t cpu_id, node_idx;
        decode_tail(tail, &cpu_id, &node_idx);
        struct mcs_node *node = &mcs_nodes[cpu_id][node_idx];

        // Wait for global next pointer to be set (may race with qspin_lock)
        struct mcs_node *next_global;
        while ((next_global = atomic_load_explicit(&node->next, memory_order_acquire)) == NULL) {
            pause();
        }

        // HIERARCHICAL QUEUE: Check for local waiter first
        struct mcs_node *next_local = atomic_load_explicit(&node->local_next, memory_order_acquire);
        struct mcs_node *next_to_wake;

        if (likely(next_local != NULL)) {
            // Local waiter available - prefer it (NUMA optimization)
            // LIKELY: local waiters common in NUMA-aware systems
            next_to_wake = next_local;
            __sync_fetch_and_add(&lock->stats.local_handoff_count, 1);
        } else {
            // No local waiter - wake remote waiter
            next_to_wake = next_global;
            __sync_fetch_and_add(&lock->stats.remote_handoff_count, 1);
        }

        // Wake the chosen waiter
        atomic_store_explicit(&next_to_wake->locked, 0, memory_order_release);

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
 * Statistics and Debugging
 * ======================================================================== */

/**
 * Print qspinlock statistics
 */
void qspin_dump_stats(struct qspinlock *lock, const char *name) {
    struct qspin_stats *s = &lock->stats;

    cprintf("=== QSpinlock Stats: %s ===\n", name);
    cprintf("Acquisitions:\n");
    cprintf("  Total:        %llu\n", s->acquire_count);

    if (s->acquire_count > 0) {
        cprintf("  Fast path:    %llu (%.1f%%)\n",
                s->fast_path_count,
                100.0 * s->fast_path_count / s->acquire_count);
        cprintf("  Slow path:    %llu (%.1f%%)\n",
                s->slow_path_count,
                100.0 * s->slow_path_count / s->acquire_count);
    }

    uint64_t total_handoffs = s->local_handoff_count + s->remote_handoff_count;
    if (total_handoffs > 0) {
        cprintf("\nNUMA Handoffs:\n");
        cprintf("  Local:        %llu (%.1f%%)\n",
                s->local_handoff_count,
                100.0 * s->local_handoff_count / total_handoffs);
        cprintf("  Remote:       %llu (%.1f%%)\n",
                s->remote_handoff_count,
                100.0 * s->remote_handoff_count / total_handoffs);
    }

    if (s->slow_path_count > 0) {
        cprintf("\nContention:\n");
        cprintf("  Max queue:    %llu waiters\n", s->max_queue_depth);
        cprintf("  Avg spin:     %llu cycles\n",
                s->total_spin_cycles / s->slow_path_count);
        cprintf("  Max spin:     %llu cycles\n", s->max_spin_cycles);
    }

    if (s->acquire_count > 0) {
        cprintf("\nHold Time:\n");
        cprintf("  Avg hold:     %llu cycles\n",
                s->total_hold_cycles / s->acquire_count);
        cprintf("  Max hold:     %llu cycles\n", s->max_hold_cycles);
    }
}

/**
 * Reset qspinlock statistics
 */
void qspin_reset_stats(struct qspinlock *lock) {
    lock->stats.fast_path_count = 0;
    lock->stats.slow_path_count = 0;
    lock->stats.local_handoff_count = 0;
    lock->stats.remote_handoff_count = 0;
    lock->stats.total_spin_cycles = 0;
    lock->stats.max_spin_cycles = 0;
    lock->stats.max_queue_depth = 0;
    lock->stats.total_hold_cycles = 0;
    lock->stats.max_hold_cycles = 0;
    lock->stats.acquire_count = 0;
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

/**
 * @file profiler.c
 * @brief Performance profiling framework with personality awareness
 * 
 * Provides CPU profiling, memory profiling, syscall profiling,
 * and personality-specific performance analysis.
 */

#include "types.h"
#include "defs.h"
#include "param.h"
#include "memlayout.h"
#include "mmu.h"
#include "x86.h"
#include "proc.h"
#include "spinlock.h"
#include "syscall_gateway.h"

// =============================================================================
// PROFILING CONFIGURATION
// =============================================================================

#define PROF_MAX_SAMPLES    100000   // Maximum profile samples
#define PROF_MAX_STACKS     10000    // Maximum unique stack traces
#define PROF_STACK_DEPTH    32       // Maximum stack depth
#define PROF_HASH_SIZE      4096     // Hash table size
#define PROF_TIMER_HZ       1000     // Profiling timer frequency

// Profiling modes
#define PROF_MODE_CPU       (1 << 0)  // CPU profiling
#define PROF_MODE_MEMORY    (1 << 1)  // Memory profiling
#define PROF_MODE_SYSCALL  (1 << 2)  // Syscall profiling
#define PROF_MODE_LOCK      (1 << 3)  // Lock contention
#define PROF_MODE_CACHE     (1 << 4)  // Cache misses
#define PROF_MODE_BRANCH    (1 << 5)  // Branch misprediction
#define PROF_MODE_IO        (1 << 6)  // I/O profiling
#define PROF_MODE_SCHED     (1 << 7)  // Scheduler profiling

// Profile event types
typedef enum {
    PROF_EVENT_TIMER,       // Timer interrupt sample
    PROF_EVENT_SYSCALL,     // System call
    PROF_EVENT_FAULT,       // Page fault
    PROF_EVENT_ALLOC,       // Memory allocation
    PROF_EVENT_FREE,        // Memory free
    PROF_EVENT_LOCK_ACQUIRE,// Lock acquisition
    PROF_EVENT_LOCK_RELEASE,// Lock release
    PROF_EVENT_LOCK_WAIT,   // Lock wait/contention
    PROF_EVENT_SCHED_IN,    // Scheduled in
    PROF_EVENT_SCHED_OUT,   // Scheduled out
    PROF_EVENT_IO_START,    // I/O operation start
    PROF_EVENT_IO_END,      // I/O operation end
} prof_event_type_t;

// =============================================================================
// DATA STRUCTURES
// =============================================================================

/**
 * Profile sample
 */
typedef struct prof_sample {
    uint64_t timestamp;             // TSC timestamp
    prof_event_type_t type;         // Event type
    pid_t pid;                      // Process ID
    pid_t tid;                      // Thread ID
    syscall_personality_t personality; // Process personality
    uint64_t pc;                    // Program counter
    uint64_t sp;                    // Stack pointer
    
    union {
        struct {
            int syscall_nr;         // Syscall number
            uint64_t duration;      // Duration in cycles
            int error;              // Error code
        } syscall;
        
        struct {
            void *addr;             // Allocation address
            size_t size;            // Allocation size
            int type;               // Allocation type
        } memory;
        
        struct {
            void *lock;             // Lock address
            uint64_t wait_time;     // Wait time in cycles
            const char *name;       // Lock name
        } lock;
        
        struct {
            uint64_t addr;          // Fault address
            int type;               // Fault type
            int handled;            // Was it handled?
        } fault;
        
        struct {
            int prev_state;         // Previous state
            int new_state;          // New state
            int cpu;                // CPU number
        } sched;
    } data;
    
    // Stack trace
    uint64_t stack[PROF_STACK_DEPTH];
    int stack_depth;
} prof_sample_t;

/**
 * Stack trace hash entry
 */
typedef struct prof_stack {
    uint64_t hash;                  // Stack trace hash
    uint64_t stack[PROF_STACK_DEPTH]; // Stack addresses
    int depth;                      // Stack depth
    uint64_t count;                 // Hit count
    uint64_t total_time;            // Total time spent
    uint64_t min_time;              // Minimum time
    uint64_t max_time;              // Maximum time
    struct prof_stack *next;       // Hash chain
} prof_stack_t;

/**
 * Per-process profiling state
 */
typedef struct prof_state {
    uint32_t mode;                  // Profiling mode
    uint32_t enabled;               // Profiling enabled
    
    // Statistics
    struct {
        uint64_t samples;           // Total samples
        uint64_t syscalls;          // Syscall count
        uint64_t faults;            // Page fault count
        uint64_t allocations;       // Memory allocations
        uint64_t lock_contentions;  // Lock contentions
        uint64_t cpu_cycles;        // Total CPU cycles
        uint64_t memory_allocated;  // Total memory allocated
        uint64_t memory_freed;      // Total memory freed
    } stats;
    
    // Syscall profiling
    struct {
        uint64_t count[512];        // Per-syscall count
        uint64_t time[512];         // Per-syscall time
        uint64_t errors[512];       // Per-syscall errors
    } syscalls;
    
    // Memory profiling
    struct {
        uint64_t alloc_count;       // Allocation count
        uint64_t free_count;        // Free count
        uint64_t current_usage;     // Current memory usage
        uint64_t peak_usage;        // Peak memory usage
        uint64_t alloc_size[16];    // Size distribution
    } memory;
    
    // Lock profiling
    struct {
        uint64_t acquisitions;      // Total acquisitions
        uint64_t contentions;       // Total contentions
        uint64_t total_wait_time;   // Total wait time
        uint64_t max_wait_time;     // Maximum wait time
    } locks;
    
    struct spinlock lock;
} prof_state_t;

/**
 * Global profiling state
 */
static struct {
    prof_sample_t *samples;         // Sample buffer
    uint32_t sample_head;           // Next write position
    uint32_t sample_tail;           // Next read position
    uint32_t sample_count;          // Total samples
    
    prof_stack_t *stacks[PROF_HASH_SIZE]; // Stack trace hash table
    uint32_t stack_count;           // Unique stack traces
    
    // Global statistics
    struct {
        uint64_t total_samples;
        uint64_t total_syscalls;
        uint64_t total_faults;
        uint64_t total_allocations;
        uint64_t by_personality[PERSONALITY_MAX];
    } stats;
    
    struct spinlock lock;
    int initialized;
} prof_global;

// =============================================================================
// STACK TRACING
// =============================================================================

/**
 * Capture stack trace
 */
static int capture_stack_trace(uint64_t *stack, int max_depth) {
    int depth = 0;
    uint64_t *ebp;
    
    // Get current frame pointer
    asm volatile("movq %%rbp, %0" : "=r"(ebp));
    
    // Walk stack frames
    while (depth < max_depth && ebp != 0) {
        // Validate frame pointer
        if ((uint64_t)ebp < KERNBASE || (uint64_t)ebp >= KERNBASE + PHYSTOP)
            break;
        
        // Get return address
        uint64_t ret_addr = ebp[1];
        if (ret_addr == 0)
            break;
        
        stack[depth++] = ret_addr;
        
        // Next frame
        ebp = (uint64_t *)ebp[0];
    }
    
    return depth;
}

/**
 * Hash stack trace
 */
static uint64_t hash_stack_trace(uint64_t *stack, int depth) {
    uint64_t hash = 0;
    
    for (int i = 0; i < depth; i++) {
        hash ^= stack[i];
        hash = (hash << 13) | (hash >> 51);
        hash *= 0x9e3779b97f4a7c15ULL;  // Golden ratio prime
    }
    
    return hash;
}

/**
 * Record stack trace
 */
static prof_stack_t *record_stack_trace(uint64_t *stack, int depth, uint64_t time) {
    uint64_t hash = hash_stack_trace(stack, depth);
    int bucket = hash % PROF_HASH_SIZE;
    
    acquire(&prof_global.lock);
    
    // Search for existing stack trace
    prof_stack_t *ps = prof_global.stacks[bucket];
    while (ps) {
        if (ps->hash == hash && ps->depth == depth &&
            memcmp(ps->stack, stack, depth * sizeof(uint64_t)) == 0) {
            // Found existing stack trace
            ps->count++;
            ps->total_time += time;
            if (time < ps->min_time) ps->min_time = time;
            if (time > ps->max_time) ps->max_time = time;
            release(&prof_global.lock);
            return ps;
        }
        ps = ps->next;
    }
    
    // Create new stack trace entry
    ps = kalloc();
    if (ps) {
        ps->hash = hash;
        ps->depth = depth;
        memcpy(ps->stack, stack, depth * sizeof(uint64_t));
        ps->count = 1;
        ps->total_time = time;
        ps->min_time = time;
        ps->max_time = time;
        ps->next = prof_global.stacks[bucket];
        prof_global.stacks[bucket] = ps;
        prof_global.stack_count++;
    }
    
    release(&prof_global.lock);
    return ps;
}

// =============================================================================
// PROFILING EVENTS
// =============================================================================

/**
 * Record profiling sample
 */
static void record_sample(prof_sample_t *sample) {
    if (!prof_global.initialized)
        return;
    
    acquire(&prof_global.lock);
    
    // Add to circular buffer
    prof_global.samples[prof_global.sample_head] = *sample;
    prof_global.sample_head = (prof_global.sample_head + 1) % PROF_MAX_SAMPLES;
    
    if (prof_global.sample_count < PROF_MAX_SAMPLES)
        prof_global.sample_count++;
    else
        prof_global.sample_tail = (prof_global.sample_tail + 1) % PROF_MAX_SAMPLES;
    
    // Update global statistics
    prof_global.stats.total_samples++;
    prof_global.stats.by_personality[sample->personality]++;
    
    switch (sample->type) {
        case PROF_EVENT_SYSCALL:
            prof_global.stats.total_syscalls++;
            break;
        case PROF_EVENT_FAULT:
            prof_global.stats.total_faults++;
            break;
        case PROF_EVENT_ALLOC:
        case PROF_EVENT_FREE:
            prof_global.stats.total_allocations++;
            break;
    }
    
    release(&prof_global.lock);
}

/**
 * Profile timer interrupt handler
 */
void prof_timer_interrupt(struct trapframe *tf) {
    struct proc *p = myproc();
    if (!p || !p->prof_state || !(p->prof_state->mode & PROF_MODE_CPU))
        return;
    
    prof_sample_t sample = {
        .timestamp = rdtsc(),
        .type = PROF_EVENT_TIMER,
        .pid = p->pid,
        .tid = p->tid,
        .personality = p->personality,
        .pc = tf->rip,
        .sp = tf->rsp
    };
    
    // Capture stack trace
    sample.stack_depth = capture_stack_trace(sample.stack, PROF_STACK_DEPTH);
    
    // Record stack trace statistics
    record_stack_trace(sample.stack, sample.stack_depth, 1);
    
    // Record sample
    record_sample(&sample);
    
    p->prof_state->stats.samples++;
}

/**
 * Profile syscall entry
 */
void prof_syscall_enter(int syscall_nr, uint64_t *args) {
    struct proc *p = myproc();
    if (!p || !p->prof_state || !(p->prof_state->mode & PROF_MODE_SYSCALL))
        return;
    
    // Mark syscall start time
    p->syscall_start_time = rdtsc();
    p->current_syscall = syscall_nr;
}

/**
 * Profile syscall exit
 */
void prof_syscall_exit(int syscall_nr, int64_t result) {
    struct proc *p = myproc();
    if (!p || !p->prof_state || !(p->prof_state->mode & PROF_MODE_SYSCALL))
        return;
    
    uint64_t duration = rdtsc() - p->syscall_start_time;
    
    prof_sample_t sample = {
        .timestamp = rdtsc(),
        .type = PROF_EVENT_SYSCALL,
        .pid = p->pid,
        .tid = p->tid,
        .personality = p->personality,
        .data.syscall = {
            .syscall_nr = syscall_nr,
            .duration = duration,
            .error = (result < 0) ? -result : 0
        }
    };
    
    // Capture stack trace
    sample.stack_depth = capture_stack_trace(sample.stack, PROF_STACK_DEPTH);
    
    // Record sample
    record_sample(&sample);
    
    // Update per-process statistics
    if (syscall_nr < 512) {
        p->prof_state->syscalls.count[syscall_nr]++;
        p->prof_state->syscalls.time[syscall_nr] += duration;
        if (result < 0)
            p->prof_state->syscalls.errors[syscall_nr]++;
    }
    
    p->prof_state->stats.syscalls++;
    p->prof_state->stats.cpu_cycles += duration;
}

/**
 * Profile memory allocation
 */
void prof_memory_alloc(void *addr, size_t size) {
    struct proc *p = myproc();
    if (!p || !p->prof_state || !(p->prof_state->mode & PROF_MODE_MEMORY))
        return;
    
    prof_sample_t sample = {
        .timestamp = rdtsc(),
        .type = PROF_EVENT_ALLOC,
        .pid = p->pid,
        .tid = p->tid,
        .personality = p->personality,
        .data.memory = {
            .addr = addr,
            .size = size,
            .type = 0  // TODO: Add allocation type
        }
    };
    
    record_sample(&sample);
    
    // Update statistics
    p->prof_state->memory.alloc_count++;
    p->prof_state->memory.current_usage += size;
    p->prof_state->stats.memory_allocated += size;
    
    if (p->prof_state->memory.current_usage > p->prof_state->memory.peak_usage)
        p->prof_state->memory.peak_usage = p->prof_state->memory.current_usage;
    
    // Size distribution
    int bucket = 0;
    size_t s = size;
    while (s > 16 && bucket < 15) {
        s >>= 1;
        bucket++;
    }
    p->prof_state->memory.alloc_size[bucket]++;
}

/**
 * Profile memory free
 */
void prof_memory_free(void *addr, size_t size) {
    struct proc *p = myproc();
    if (!p || !p->prof_state || !(p->prof_state->mode & PROF_MODE_MEMORY))
        return;
    
    prof_sample_t sample = {
        .timestamp = rdtsc(),
        .type = PROF_EVENT_FREE,
        .pid = p->pid,
        .tid = p->tid,
        .personality = p->personality,
        .data.memory = {
            .addr = addr,
            .size = size,
            .type = 0
        }
    };
    
    record_sample(&sample);
    
    // Update statistics
    p->prof_state->memory.free_count++;
    p->prof_state->memory.current_usage -= size;
    p->prof_state->stats.memory_freed += size;
}

/**
 * Profile lock contention
 */
void prof_lock_contention(struct spinlock *lock, uint64_t wait_time) {
    struct proc *p = myproc();
    if (!p || !p->prof_state || !(p->prof_state->mode & PROF_MODE_LOCK))
        return;
    
    prof_sample_t sample = {
        .timestamp = rdtsc(),
        .type = PROF_EVENT_LOCK_WAIT,
        .pid = p->pid,
        .tid = p->tid,
        .personality = p->personality,
        .data.lock = {
            .lock = lock,
            .wait_time = wait_time,
            .name = lock->name
        }
    };
    
    // Capture stack trace
    sample.stack_depth = capture_stack_trace(sample.stack, PROF_STACK_DEPTH);
    
    record_sample(&sample);
    
    // Update statistics
    p->prof_state->locks.contentions++;
    p->prof_state->locks.total_wait_time += wait_time;
    if (wait_time > p->prof_state->locks.max_wait_time)
        p->prof_state->locks.max_wait_time = wait_time;
    p->prof_state->stats.lock_contentions++;
}

// =============================================================================
// PROFILING CONTROL
// =============================================================================

/**
 * Enable profiling for process
 */
int prof_enable(struct proc *p, uint32_t mode) {
    if (!p)
        return -EINVAL;
    
    // Allocate profiling state if needed
    if (!p->prof_state) {
        p->prof_state = kalloc();
        if (!p->prof_state)
            return -ENOMEM;
        
        memset(p->prof_state, 0, sizeof(prof_state_t));
        initlock(&p->prof_state->lock, "profiler");
    }
    
    p->prof_state->mode = mode;
    p->prof_state->enabled = 1;
    
    cprintf("Profiling enabled for PID %d (mode=0x%x personality=%s)\n",
            p->pid, mode, get_personality_name(p->personality));
    
    return 0;
}

/**
 * Disable profiling for process
 */
int prof_disable(struct proc *p) {
    if (!p || !p->prof_state)
        return -EINVAL;
    
    p->prof_state->enabled = 0;
    
    cprintf("Profiling disabled for PID %d\n", p->pid);
    
    return 0;
}

// =============================================================================
// REPORTING
// =============================================================================

/**
 * Generate CPU profile report
 */
void prof_report_cpu(struct proc *p) {
    if (!p || !p->prof_state)
        return;
    
    cprintf("\n=== CPU Profile Report for PID %d (%s) ===\n",
            p->pid, get_personality_name(p->personality));
    
    cprintf("Total samples: %llu\n", p->prof_state->stats.samples);
    cprintf("Total CPU cycles: %llu\n", p->prof_state->stats.cpu_cycles);
    
    // Find hot spots
    cprintf("\nTop 10 Hot Spots:\n");
    cprintf("%-8s %-8s %-16s\n", "Count", "Percent", "Address");
    cprintf("-------- -------- ----------------\n");
    
    // TODO: Aggregate samples by PC and report top functions
}

/**
 * Generate syscall profile report
 */
void prof_report_syscalls(struct proc *p) {
    if (!p || !p->prof_state)
        return;
    
    cprintf("\n=== Syscall Profile Report for PID %d (%s) ===\n",
            p->pid, get_personality_name(p->personality));
    
    cprintf("Total syscalls: %llu\n", p->prof_state->stats.syscalls);
    
    // Sort syscalls by time
    struct {
        int nr;
        uint64_t count;
        uint64_t time;
        uint64_t errors;
    } top[10] = {0};
    
    for (int i = 0; i < 512; i++) {
        if (p->prof_state->syscalls.count[i] == 0)
            continue;
        
        // Insert into top 10
        for (int j = 0; j < 10; j++) {
            if (p->prof_state->syscalls.time[i] > top[j].time) {
                // Shift down
                for (int k = 9; k > j; k--)
                    top[k] = top[k-1];
                
                top[j].nr = i;
                top[j].count = p->prof_state->syscalls.count[i];
                top[j].time = p->prof_state->syscalls.time[i];
                top[j].errors = p->prof_state->syscalls.errors[i];
                break;
            }
        }
    }
    
    cprintf("\nTop 10 Syscalls by Time:\n");
    cprintf("%-20s %8s %12s %8s %8s\n", 
            "Syscall", "Count", "Total(cycles)", "Avg(cycles)", "Errors");
    cprintf("-------------------- -------- ------------ -------- --------\n");
    
    for (int i = 0; i < 10 && top[i].count > 0; i++) {
        const char *name = get_syscall_name(p->personality, top[i].nr);
        uint64_t avg = top[i].time / top[i].count;
        
        cprintf("%-20s %8llu %12llu %8llu %8llu\n",
                name, top[i].count, top[i].time, avg, top[i].errors);
    }
}

/**
 * Generate memory profile report
 */
void prof_report_memory(struct proc *p) {
    if (!p || !p->prof_state)
        return;
    
    cprintf("\n=== Memory Profile Report for PID %d (%s) ===\n",
            p->pid, get_personality_name(p->personality));
    
    cprintf("Current usage: %llu bytes\n", p->prof_state->memory.current_usage);
    cprintf("Peak usage: %llu bytes\n", p->prof_state->memory.peak_usage);
    cprintf("Total allocated: %llu bytes\n", p->prof_state->stats.memory_allocated);
    cprintf("Total freed: %llu bytes\n", p->prof_state->stats.memory_freed);
    cprintf("Allocations: %llu\n", p->prof_state->memory.alloc_count);
    cprintf("Frees: %llu\n", p->prof_state->memory.free_count);
    
    cprintf("\nAllocation Size Distribution:\n");
    cprintf("Size Range          Count\n");
    cprintf("------------------- --------\n");
    
    for (int i = 0; i < 16; i++) {
        if (p->prof_state->memory.alloc_size[i] == 0)
            continue;
        
        uint64_t min_size = (i == 0) ? 0 : (16ULL << (i - 1));
        uint64_t max_size = 16ULL << i;
        
        cprintf("%8llu - %8llu: %llu\n",
                min_size, max_size, p->prof_state->memory.alloc_size[i]);
    }
}

/**
 * Generate complete profile report
 */
void prof_report(struct proc *p) {
    if (!p || !p->prof_state)
        return;
    
    cprintf("\n" "=".repeat(60) "\n");
    cprintf("PERFORMANCE PROFILE REPORT\n");
    cprintf("Process: %d (%s)\n", p->pid, p->name);
    cprintf("Personality: %s\n", get_personality_name(p->personality));
    cprintf("=".repeat(60) "\n");
    
    if (p->prof_state->mode & PROF_MODE_CPU)
        prof_report_cpu(p);
    
    if (p->prof_state->mode & PROF_MODE_SYSCALL)
        prof_report_syscalls(p);
    
    if (p->prof_state->mode & PROF_MODE_MEMORY)
        prof_report_memory(p);
    
    if (p->prof_state->mode & PROF_MODE_LOCK) {
        cprintf("\n=== Lock Contention Report ===\n");
        cprintf("Total contentions: %llu\n", p->prof_state->locks.contentions);
        cprintf("Total wait time: %llu cycles\n", p->prof_state->locks.total_wait_time);
        cprintf("Max wait time: %llu cycles\n", p->prof_state->locks.max_wait_time);
        if (p->prof_state->locks.contentions > 0) {
            cprintf("Average wait time: %llu cycles\n",
                    p->prof_state->locks.total_wait_time / p->prof_state->locks.contentions);
        }
    }
    
    cprintf("\n=== Global Statistics ===\n");
    cprintf("Total samples: %llu\n", prof_global.stats.total_samples);
    cprintf("Unique stack traces: %u\n", prof_global.stack_count);
    
    cprintf("\nSamples by Personality:\n");
    for (int i = 0; i < PERSONALITY_MAX; i++) {
        if (prof_global.stats.by_personality[i] > 0) {
            cprintf("  %s: %llu\n",
                    get_personality_name(i),
                    prof_global.stats.by_personality[i]);
        }
    }
}

// =============================================================================
// SYSTEM CALLS
// =============================================================================

/**
 * System call: Start profiling
 */
long sys_prof_start(pid_t pid, uint32_t mode) {
    struct proc *p;
    
    if (pid == 0) {
        p = myproc();
    } else {
        p = find_proc_by_pid(pid);
        if (!p)
            return -ESRCH;
        
        // Check permissions
        if (p->uid != myproc()->uid && myproc()->uid != 0)
            return -EPERM;
    }
    
    return prof_enable(p, mode);
}

/**
 * System call: Stop profiling
 */
long sys_prof_stop(pid_t pid) {
    struct proc *p;
    
    if (pid == 0) {
        p = myproc();
    } else {
        p = find_proc_by_pid(pid);
        if (!p)
            return -ESRCH;
        
        // Check permissions
        if (p->uid != myproc()->uid && myproc()->uid != 0)
            return -EPERM;
    }
    
    return prof_disable(p);
}

/**
 * System call: Get profile data
 */
long sys_prof_get(pid_t pid, void *buf, size_t size) {
    struct proc *p;
    
    if (pid == 0) {
        p = myproc();
    } else {
        p = find_proc_by_pid(pid);
        if (!p)
            return -ESRCH;
        
        // Check permissions
        if (p->uid != myproc()->uid && myproc()->uid != 0)
            return -EPERM;
    }
    
    if (!p->prof_state)
        return -EINVAL;
    
    // Copy profile data to user buffer
    // TODO: Implement data serialization
    
    // For now, generate report to console
    prof_report(p);
    
    return 0;
}

// =============================================================================
// INITIALIZATION
// =============================================================================

/**
 * Initialize profiling subsystem
 */
void init_profiler(void) {
    // Allocate sample buffer
    prof_global.samples = kalloc_pages(
        (PROF_MAX_SAMPLES * sizeof(prof_sample_t) + PGSIZE - 1) / PGSIZE);
    
    if (!prof_global.samples) {
        panic("Failed to allocate profile sample buffer");
    }
    
    memset(prof_global.samples, 0, PROF_MAX_SAMPLES * sizeof(prof_sample_t));
    initlock(&prof_global.lock, "profiler");
    
    prof_global.initialized = 1;
    
    cprintf("Performance profiler initialized\n");
    cprintf("  Sample buffer: %d samples\n", PROF_MAX_SAMPLES);
    cprintf("  Stack traces: %d max unique\n", PROF_MAX_STACKS);
    cprintf("  Profiling modes:\n");
    cprintf("    - CPU profiling (sampling)\n");
    cprintf("    - Syscall profiling\n");
    cprintf("    - Memory profiling\n");
    cprintf("    - Lock contention\n");
    cprintf("  Personality-aware profiling enabled\n");
}
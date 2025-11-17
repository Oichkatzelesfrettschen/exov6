# Phase 3 Execution Plan: LWKT Token Implementation

**Timeline:** Weeks 5-6
**Objective:** Implement DragonFlyBSD-inspired LWKT tokens for exokernel capability traversal
**Status:** 🚀 Ready to execute

---

## Overview

LWKT (Light-Weight Kernel Thread) tokens are "soft locks" that provide:
- **CPU ownership** - Tokens are held by CPUs, not threads
- **Automatic release** - Released when thread blocks/yields
- **Low overhead** - No expensive atomic operations in fast path
- **Serialization** - Ensure single accessor to data structures
- **Perfect for exokernel** - Capability table traversal, metadata access

Unlike traditional locks:
- No sleep/wakeup mechanism
- No priority inheritance
- Released automatically on context switch
- Extremely low overhead

---

## Phase 3 Architecture

### Key Concepts

**Token Ownership:**
- Each token has one owner CPU (or none)
- Multiple tokens can be held simultaneously
- Tokens automatically released on thread block

**Token Pool:**
- Hash-based distribution (256 slots)
- Reduces contention via partitioning
- Static allocation (no dynamic memory)

**Use Cases:**
- Capability table traversal
- Page table metadata access
- Per-CPU data structure access
- Exokernel resource management

---

## Detailed Task Breakdown

### Step 3.1: LWKT Token Data Structures (Day 1)

#### Task 3.1.1: Enhance lwkt_token structure
**File:** `include/exo_lock.h`
**Lines:** ~80

Already exists with basic structure - enhance with:

```c
struct lwkt_token {
    _Atomic uint32_t owner_cpu;      /**< CPU ID holding token (NCPU = free) */
    uint32_t hash;                   /**< Token pool hash */
    const char *name;                /**< Debug name */
    uint64_t acquire_tsc;            /**< Timestamp of acquisition */

    /* Statistics */
    uint64_t acquire_count;          /**< Total acquisitions */
    uint64_t contention_count;       /**< Times had to wait */
    uint64_t total_hold_cycles;      /**< Total cycles held */
    uint64_t max_hold_cycles;        /**< Longest hold time */

    /* Per-CPU acquisition tracking */
    uint64_t cpu_acquire_count[NCPU]; /**< Acquisitions per CPU */
} __attribute__((aligned(128)));
```

**Subtasks:**
1. Add statistics fields
2. Add per-CPU tracking
3. Ensure cache alignment
4. Add compile-time size checks

#### Task 3.1.2: Define token pool
**File:** `include/exo_lock.h`
**Lines:** ~20

```c
/* Token pool for hash-based distribution */
#define TOKEN_POOL_SIZE 256
#define TOKEN_POOL_HASH_BITS 8

/* Per-CPU token ownership tracking */
struct cpu_token_list {
    struct lwkt_token *tokens[MAX_TOKENS_PER_CPU];
    uint32_t count;
} __attribute__((aligned(64)));

extern struct lwkt_token token_pool[TOKEN_POOL_SIZE];
extern struct cpu_token_list cpu_tokens[NCPU];

#define MAX_TOKENS_PER_CPU 16  /**< Max simultaneous tokens per CPU */
```

---

### Step 3.2: Core Token Operations (Day 2-3)

#### Task 3.2.1: Implement token_init()
**File:** `kernel/sync/lwkt_token.c`
**Lines:** ~30

```c
void token_init(struct lwkt_token *token, const char *name) {
    atomic_store(&token->owner_cpu, NCPU);  // NCPU = free
    token->hash = hash_ptr(token);
    token->name = name;
    token->acquire_tsc = 0;
    token->acquire_count = 0;
    token->contention_count = 0;
    token->total_hold_cycles = 0;
    token->max_hold_cycles = 0;

    for (int i = 0; i < NCPU; i++) {
        token->cpu_acquire_count[i] = 0;
    }
}
```

#### Task 3.2.2: Implement token_acquire()
**File:** `kernel/sync/lwkt_token.c`
**Lines:** ~80

**Algorithm:**
```c
void token_acquire(struct lwkt_token *token) {
    uint32_t my_cpu = mycpu() - cpus;

    // Fast path: already own it
    if (atomic_load(&token->owner_cpu) == my_cpu) {
        return;  // Already own it
    }

    // Slow path: acquire from another CPU
    while (1) {
        uint32_t expected = NCPU;  // Free

        if (atomic_compare_exchange_strong(&token->owner_cpu, &expected, my_cpu)) {
            // Acquired!
            token->acquire_tsc = rdtsc();
            token->acquire_count++;
            token->cpu_acquire_count[my_cpu]++;

            // Add to CPU's token list
            cpu_token_add(my_cpu, token);

            return;
        }

        // Contention - wait for current owner to release
        token->contention_count++;

        // Spin with backoff
        int backoff = 10;
        while (atomic_load(&token->owner_cpu) != NCPU) {
            for (int i = 0; i < backoff; i++) {
                pause();
            }
            backoff = min(backoff * 2, 1000);
        }
    }
}
```

#### Task 3.2.3: Implement token_release()
**File:** `kernel/sync/lwkt_token.c`
**Lines:** ~40

```c
void token_release(struct lwkt_token *token) {
    uint32_t my_cpu = mycpu() - cpus;

    // Verify we own it
    if (atomic_load(&token->owner_cpu) != my_cpu) {
        panic("token_release: not owner");
    }

    // Track hold time
    uint64_t hold_cycles = rdtsc() - token->acquire_tsc;
    token->total_hold_cycles += hold_cycles;

    if (hold_cycles > token->max_hold_cycles) {
        token->max_hold_cycles = hold_cycles;
    }

    // Remove from CPU's token list
    cpu_token_remove(my_cpu, token);

    // Release
    atomic_store(&token->owner_cpu, NCPU);
}
```

#### Task 3.2.4: Implement token_release_all()
**File:** `kernel/sync/lwkt_token.c`
**Lines:** ~30

**Critical for context switch:**
```c
void token_release_all(void) {
    uint32_t my_cpu = mycpu() - cpus;
    struct cpu_token_list *list = &cpu_tokens[my_cpu];

    // Release all tokens held by this CPU
    for (int i = 0; i < list->count; i++) {
        struct lwkt_token *token = list->tokens[i];

        // Track hold time
        uint64_t hold_cycles = rdtsc() - token->acquire_tsc;
        token->total_hold_cycles += hold_cycles;

        if (hold_cycles > token->max_hold_cycles) {
            token->max_hold_cycles = hold_cycles;
        }

        // Release
        atomic_store(&token->owner_cpu, NCPU);
    }

    list->count = 0;
}
```

---

### Step 3.3: Token Pool Management (Day 4)

#### Task 3.3.1: Implement token pool initialization
**File:** `kernel/sync/lwkt_token.c`
**Lines:** ~40

```c
struct lwkt_token token_pool[TOKEN_POOL_SIZE];
struct cpu_token_list cpu_tokens[NCPU];

void token_pool_init(void) {
    // Initialize token pool
    for (int i = 0; i < TOKEN_POOL_SIZE; i++) {
        token_init(&token_pool[i], "pool_token");
        token_pool[i].hash = i;
    }

    // Initialize per-CPU token lists
    for (int i = 0; i < NCPU; i++) {
        cpu_tokens[i].count = 0;
        for (int j = 0; j < MAX_TOKENS_PER_CPU; j++) {
            cpu_tokens[i].tokens[j] = NULL;
        }
    }

    cprintf("lwkt_token: initialized pool with %d tokens\n", TOKEN_POOL_SIZE);
}
```

#### Task 3.3.2: Implement token pool lookup
**File:** `kernel/sync/lwkt_token.c`
**Lines:** ~30

```c
static uint32_t hash_ptr(void *ptr) {
    uintptr_t val = (uintptr_t)ptr;
    val = (val >> 6) ^ (val >> 12) ^ (val >> 18);
    return val & (TOKEN_POOL_SIZE - 1);
}

struct lwkt_token *token_pool_get(void *resource) {
    uint32_t hash = hash_ptr(resource);
    return &token_pool[hash];
}
```

#### Task 3.3.3: Implement CPU token list management
**File:** `kernel/sync/lwkt_token.c`
**Lines:** ~60

```c
static void cpu_token_add(uint32_t cpu, struct lwkt_token *token) {
    struct cpu_token_list *list = &cpu_tokens[cpu];

    if (list->count >= MAX_TOKENS_PER_CPU) {
        panic("cpu_token_add: too many tokens");
    }

    list->tokens[list->count++] = token;
}

static void cpu_token_remove(uint32_t cpu, struct lwkt_token *token) {
    struct cpu_token_list *list = &cpu_tokens[cpu];

    for (int i = 0; i < list->count; i++) {
        if (list->tokens[i] == token) {
            // Remove by shifting
            for (int j = i; j < list->count - 1; j++) {
                list->tokens[j] = list->tokens[j + 1];
            }
            list->count--;
            return;
        }
    }

    panic("cpu_token_remove: token not found");
}
```

---

### Step 3.4: Integration with Scheduler (Day 5)

#### Task 3.4.1: Add token_release_all() to context switch
**File:** `kernel/proc.c` (or scheduler)
**Lines:** ~10

```c
// In scheduler/context switch:
void sched(void) {
    // ... existing code ...

    // Release all LWKT tokens before context switch
    token_release_all();

    // ... continue with context switch ...
}
```

#### Task 3.4.2: Add token verification
**File:** `kernel/sync/lwkt_token.c`
**Lines:** ~30

```c
int token_holding(struct lwkt_token *token) {
    uint32_t my_cpu = mycpu() - cpus;
    return atomic_load(&token->owner_cpu) == my_cpu;
}

void token_assert_held(struct lwkt_token *token) {
    if (!token_holding(token)) {
        panic("token_assert_held: token not held");
    }
}
```

---

### Step 3.5: Testing and Benchmarking (Day 6-7)

#### Task 3.5.1: Unit tests
**File:** `kernel/sync/test_lwkt_token.c`
**Lines:** ~600

**Test cases:**
1. Initialization
2. Single acquire/release
3. Multiple tokens per CPU
4. Automatic release on context switch
5. Contention handling
6. Statistics tracking
7. Pool distribution
8. Hash collision handling
9. Max tokens per CPU limit
10. Concurrent access from multiple CPUs

#### Task 3.5.2: Microbenchmarks
**File:** `kernel/sync/bench_lwkt_token.c`
**Lines:** ~500

**Benchmarks:**
1. Acquire/release latency (owned)
2. Acquire/release latency (unowned)
3. Contention overhead
4. Pool lookup overhead
5. Multi-token overhead
6. Context switch impact

---

### Step 3.6: Documentation (Day 8)

#### Task 3.6.1: Design documentation
**File:** `docs/LWKT_TOKEN_DESIGN.md`
**Lines:** ~400

**Sections:**
- Overview
- DragonFlyBSD inspiration
- Token ownership model
- Automatic release mechanism
- Pool-based distribution
- Use cases in exokernel
- Performance analysis
- Integration guide

#### Task 3.6.2: API documentation
**File:** `docs/LWKT_TOKEN_API.md`
**Lines:** ~200

---

## Key Design Decisions

### 1. CPU Ownership vs Thread Ownership
**Decision:** CPU ownership
**Rationale:** Simpler, faster, automatic release on context switch

### 2. Spin vs Block
**Decision:** Pure spin (no blocking)
**Rationale:** Tokens for short critical sections only

### 3. Pool Size
**Decision:** 256 tokens
**Rationale:** Power of 2, good distribution, minimal memory

### 4. Hash Function
**Decision:** Pointer-based hash with XOR folding
**Rationale:** Fast, good distribution, no table lookup

---

## Performance Targets

| Metric | Target | Measurement |
|--------|--------|-------------|
| Acquire (owned) | < 5ns | RDTSC |
| Acquire (unowned) | < 20ns | RDTSC |
| Release | < 10ns | RDTSC |
| Pool lookup | < 5ns | RDTSC |
| Contention overhead | < 100ns | RDTSC |

---

## Integration Points

### Exokernel Use Cases

1. **Capability Table Access**
```c
struct lwkt_token *cap_token = token_pool_get(&proc->cap_table);
token_acquire(cap_token);
// Access capability table
token_release(cap_token);
```

2. **Page Table Metadata**
```c
token_acquire(page->metadata_token);
// Update page metadata
token_release(page->metadata_token);
```

3. **Per-CPU Resource Management**
```c
token_acquire(cpu->resource_token);
// Access per-CPU resources
token_release(cpu->resource_token);
```

---

## Comparison with Other Locks

| Feature | LWKT Token | Spinlock | Adaptive Mutex |
|---------|-----------|----------|----------------|
| Ownership | CPU | Thread | Thread |
| Auto-release | Yes | No | No |
| Blocking | No | No | Optional |
| Priority Inheritance | No | No | Optional |
| Overhead | Lowest | Low | Medium |
| Use Case | Very short | Short | Medium |

---

## Timeline

**Day 1:** Data structures (Tasks 3.1.1-3.1.2)
**Day 2-3:** Core operations (Tasks 3.2.1-3.2.4)
**Day 4:** Pool management (Tasks 3.3.1-3.3.3)
**Day 5:** Scheduler integration (Tasks 3.4.1-3.4.2)
**Day 6-7:** Testing (Tasks 3.5.1-3.5.2)
**Day 8:** Documentation (Tasks 3.6.1-3.6.2)

---

## Success Metrics

- **Code:** ~800 lines of production code
- **Tests:** ~1,100 lines of test code
- **Docs:** ~600 lines of documentation
- **Commits:** ~6-8 commits
- **All tests:** PASSING ✅
- **Performance:** MEETS TARGETS ✅

---

**Status:** Ready to execute
**Next Action:** Begin Task 3.1.1 (Enhance lwkt_token structure)

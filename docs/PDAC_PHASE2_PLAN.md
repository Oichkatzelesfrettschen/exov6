# PDAC Phase 2: Granular Implementation Plan
## seL4-Cap'nProto Hybrid Capability System

**Goal**: Create a verifiable, performant capability system combining seL4 simplicity, Cap'n Proto zero-copy IPC, and lambda-based dynamic rights.

**Timeline**: 2 weeks (assuming 4-6 hours/day)

---

## Phase 2.1: Core Data Structures & API Design (Days 1-2)

### Task 2.1.1: Define capability_v2 core structure
**File**: `include/capability_v2.h`
**Estimated time**: 2 hours

**Subtasks**:
- [ ] Define `struct capability_v2` with seL4-style fields:
  - `uint64_t resource_id` (physical resource handle)
  - `uint32_t owner_pid` (owning process)
  - `uint32_t refcount` (reference counting for safe delegation)
  - `uint32_t cap_type` (memory page, device port, IPC endpoint, etc.)
- [ ] Add PDAC extensions:
  - `resource_vector_t quota` (8D resource quotas using octonions)
  - `cap_formula_t rights_fn` (function pointer for dynamic rights)
- [ ] Add Cap'n Proto metadata:
  - `uint32_t schema_id` (type tag for IPC messages)
  - `void *capnp_buffer` (pointer to serialized data)
- [ ] Add token bucket for rate limiting:
  - `uint64_t tokens` (Q16.16 fixed-point available tokens)
  - `uint64_t refill_rate` (tokens per millisecond)
  - `uint32_t rng_seed` (stochastic variance seed)
- [ ] Document pedagogical rationale for each field

**Success criteria**: Header compiles cleanly, all fields documented with inline comments

---

### Task 2.1.2: Define capability table and access API
**File**: `include/capability_v2.h`
**Estimated time**: 3 hours

**Subtasks**:
- [ ] Define global capability table:
  ```c
  #define CAP_TABLE_V2_SIZE 4096
  extern struct capability_v2 cap_table_v2[CAP_TABLE_V2_SIZE];
  ```
- [ ] Define capability table metadata:
  - Free list for O(1) allocation
  - Generation counters to detect use-after-free
  - Lock-free bitmap for slot allocation
- [ ] Design core API functions (declarations only):
  - `int capv2_alloc(uint32_t owner_pid, uint64_t resource_id, uint32_t cap_type)`
  - `int capv2_free(int cap_slot)`
  - `int capv2_grant(int cap_slot, uint32_t recipient_pid)`
  - `int capv2_revoke(int cap_slot)`
  - `int capv2_derive(int parent_slot, resource_vector_t child_quota)`
  - `uint32_t capv2_check_rights(int cap_slot, uint32_t context)`
- [ ] Define error codes:
  - `CAPV2_ERR_INVALID_SLOT`
  - `CAPV2_ERR_NO_PERMISSION`
  - `CAPV2_ERR_TABLE_FULL`
  - `CAPV2_ERR_REFCOUNT_OVERFLOW`
- [ ] Add comprehensive API documentation with examples

**Success criteria**: API design reviewed against seL4 capability model, clear separation of concerns

---

### Task 2.1.3: Define capability types and rights constants
**File**: `include/capability_v2.h`
**Estimated time**: 1 hour

**Subtasks**:
- [ ] Define capability types:
  ```c
  typedef enum {
      CAP_TYPE_NULL = 0,
      CAP_TYPE_MEMORY_PAGE,
      CAP_TYPE_DEVICE_PORT,
      CAP_TYPE_IPC_ENDPOINT,
      CAP_TYPE_IRQ_HANDLER,
      CAP_TYPE_PROCESS_CONTROL,
      CAP_TYPE_RESOURCE_QUOTA,
  } cap_type_t;
  ```
- [ ] Define capability rights bitmask:
  ```c
  #define CAP_RIGHT_READ    (1 << 0)
  #define CAP_RIGHT_WRITE   (1 << 1)
  #define CAP_RIGHT_EXECUTE (1 << 2)
  #define CAP_RIGHT_GRANT   (1 << 3)  /* Can delegate to others */
  #define CAP_RIGHT_REVOKE  (1 << 4)  /* Can revoke children */
  #define CAP_RIGHT_DERIVE  (1 << 5)  /* Can create derived caps */
  ```
- [ ] Define convenience macros:
  - `CAP_RIGHTS_FULL` (all rights)
  - `CAP_RIGHTS_RO` (read-only)
  - `CAP_RIGHTS_RW` (read-write, no grant)

**Success criteria**: Types match seL4 ontology, rights are composable

---

## Phase 2.2: Basic Capability Table Implementation (Days 3-5)

### Task 2.2.1: Implement capability table initialization
**File**: `kernel/capability_v2.c`
**Estimated time**: 2 hours

**Subtasks**:
- [ ] Implement `capv2_table_init()`:
  - Initialize all slots to `CAP_TYPE_NULL`
  - Set up free list (linked list through empty slots)
  - Initialize generation counters to 0
  - Initialize table lock (spinlock or qspinlock)
- [ ] Implement `capv2_slot_alloc()` (internal helper):
  - Pop from free list (O(1))
  - Increment generation counter
  - Return slot index with generation embedded
- [ ] Implement `capv2_slot_free()` (internal helper):
  - Validate generation counter
  - Zero out slot contents
  - Push back to free list
- [ ] Add debugging helper `capv2_print_table_stats()`:
  - Print free/used slot counts
  - Print per-type counts
  - Print refcount histogram

**Success criteria**: 100% slot allocation/deallocation coverage, no memory leaks

---

### Task 2.2.2: Implement core capability operations
**File**: `kernel/capability_v2.c`
**Estimated time**: 4 hours

**Subtasks**:
- [ ] Implement `capv2_alloc()`:
  - Allocate slot from free list
  - Initialize capability with owner, resource, type
  - Set default quota (copy from parent or system default)
  - Set default rights (based on type)
  - Initialize refcount to 1
- [ ] Implement `capv2_free()`:
  - Check refcount == 0
  - Check caller has permission (owner or REVOKE right)
  - Release resource (call resource-specific cleanup)
  - Free slot
- [ ] Implement `capv2_grant()`:
  - Check caller has GRANT right
  - Increment refcount
  - Create new slot for recipient
  - Copy capability (with possibly reduced rights)
  - Validate quota derivation doesn't exceed parent
- [ ] Implement `capv2_revoke()`:
  - Check caller has REVOKE right or is owner
  - Decrement refcount
  - If refcount hits 0, call `capv2_free()`
- [ ] Implement `capv2_derive()`:
  - Check caller has DERIVE right
  - Validate child quota <= parent quota using `resource_vector_fits()`
  - Create derived capability with reduced quota
  - Maintain parent-child relationship (for revocation tree)

**Success criteria**: All operations validate permissions correctly, resource vectors integrated

---

### Task 2.2.3: Add capability table locking and concurrency
**File**: `kernel/capability_v2.c`
**Estimated time**: 3 hours

**Subtasks**:
- [ ] Add per-slot fine-grained locking:
  - Use existing `qspinlock` from exov6
  - Embed lock in each capability slot
  - Implement lock ordering to prevent deadlocks
- [ ] Implement capability acquisition protocol:
  - `capv2_acquire(slot)`: Take lock, validate, return pointer
  - `capv2_release(slot)`: Release lock
  - RAII-style helper macros for automatic release
- [ ] Add RCU-style read paths for common operations:
  - Read-only rights checks don't need full lock
  - Use generation counters for validation
- [ ] Add comprehensive concurrency tests:
  - Parallel grant/revoke stress test
  - Race condition validation
  - Deadlock prevention verification

**Success criteria**: No data races under concurrent access (verify with ThreadSanitizer if available)

---

## Phase 2.3: Lambda Formula DSL for Dynamic Rights (Days 6-8)

### Task 2.3.1: Design lambda formula system
**File**: `include/cap_formula.h`
**Estimated time**: 3 hours

**Subtasks**:
- [ ] Define formula function pointer type:
  ```c
  typedef uint32_t (*cap_formula_t)(struct cap_formula_context *ctx);
  ```
- [ ] Define formula evaluation context:
  ```c
  struct cap_formula_context {
      uint32_t user_id;           /* Caller's UID */
      uint32_t time_ms;           /* Elapsed time since cap creation */
      uint32_t tokens_remaining;  /* Token bucket balance */
      uint64_t access_count;      /* Number of times cap used */
      resource_vector_t consumed; /* Resources consumed so far */
  };
  ```
- [ ] Define formula combinator types:
  - `cap_formula_constant(rights)` - Always return fixed rights
  - `cap_formula_and(f1, f2)` - Intersection of two formulas
  - `cap_formula_or(f1, f2)` - Union of two formulas
  - `cap_formula_time_decay(initial, decay_rate)` - Time-degrading rights
  - `cap_formula_quota_based(quota_threshold)` - Rights based on token bucket
- [ ] Document pedagogical examples:
  - Time-based access (temporary capabilities)
  - User-level access (root vs. regular users)
  - Quota-based access (pay-per-use capabilities)

**Success criteria**: Formula DSL expressive enough for real-world policies

---

### Task 2.3.2: Implement standard formula functions
**File**: `kernel/cap_formula.c`
**Estimated time**: 4 hours

**Subtasks**:
- [ ] Implement `cap_formula_constant()`:
  ```c
  uint32_t cap_formula_constant(struct cap_formula_context *ctx) {
      return ctx->initial_rights;  /* Store in context */
  }
  ```
- [ ] Implement `cap_formula_time_decay()`:
  ```c
  uint32_t cap_formula_time_decay(struct cap_formula_context *ctx) {
      /* Rights = initial * exp(-decay_rate * time) */
      /* Use Q16.16 fixed-point approximation */
      q16_t decay_factor = q16_exp(q16_mul(
          q16_from_int(-decay_rate),
          q16_from_int(ctx->time_ms / 1000)
      ));
      /* Multiply rights by decay factor */
      /* ... implementation ... */
  }
  ```
- [ ] Implement `cap_formula_user_based()`:
  ```c
  uint32_t cap_formula_user_based(struct cap_formula_context *ctx) {
      if (ctx->user_id == 0) return CAP_RIGHTS_FULL;  /* Root */
      if (ctx->user_id < 1000) return CAP_RIGHTS_RW;  /* System */
      return CAP_RIGHTS_RO;  /* Regular users */
  }
  ```
- [ ] Implement `cap_formula_quota_based()`:
  ```c
  uint32_t cap_formula_quota_based(struct cap_formula_context *ctx) {
      if (ctx->tokens_remaining > 1000) return CAP_RIGHT_READ | CAP_RIGHT_WRITE;
      if (ctx->tokens_remaining > 100) return CAP_RIGHT_READ;
      return 0;  /* Out of quota */
  }
  ```
- [ ] Implement formula composition:
  - `cap_formula_and_impl()` - bitwise AND of two formulas
  - `cap_formula_or_impl()` - bitwise OR of two formulas
  - Function pointer registration system

**Success criteria**: All standard formulas produce expected results, composition works correctly

---

### Task 2.3.3: Integrate formulas into capability system
**File**: `kernel/capability_v2.c`
**Estimated time**: 2 hours

**Subtasks**:
- [ ] Modify `capv2_check_rights()` to evaluate formula:
  ```c
  uint32_t capv2_check_rights(int cap_slot, uint32_t requested_rights) {
      struct capability_v2 *cap = &cap_table_v2[cap_slot];

      /* Build evaluation context */
      struct cap_formula_context ctx = {
          .user_id = current_proc->uid,
          .time_ms = timer_elapsed_ms(cap->creation_time),
          .tokens_remaining = cap->rate_limit.tokens,
          .access_count = cap->access_count,
          .consumed = cap->consumed_resources,
      };

      /* Evaluate formula to get dynamic rights */
      uint32_t actual_rights = cap->rights_fn(&ctx);

      /* Check if requested rights are subset of actual rights */
      return (requested_rights & actual_rights) == requested_rights;
  }
  ```
- [ ] Add formula field to `capv2_alloc()`:
  - Default to `cap_formula_constant` with full rights
  - Allow caller to specify custom formula
- [ ] Add syscall for updating formula:
  - `sys_capv2_set_formula(cap_slot, formula_id, params)`
  - Validate caller has DERIVE right
  - Apply new formula

**Success criteria**: Formulas evaluated correctly on every capability access

---

## Phase 2.4: Token Bucket Rate Limiting (Days 9-10)

### Task 2.4.1: Implement token bucket algorithm
**File**: `kernel/token_bucket.c`
**Estimated time**: 3 hours

**Subtasks**:
- [ ] Define token bucket structure (already in `capability_v2`):
  ```c
  struct token_bucket {
      uint64_t tokens;         /* Q16.16 fixed-point */
      uint64_t capacity;       /* Maximum tokens */
      uint64_t refill_rate;    /* Tokens per millisecond */
      uint64_t last_refill_ms; /* Timestamp of last refill */
      uint32_t rng_seed;       /* Stochastic variance */
  };
  ```
- [ ] Implement `token_bucket_init()`:
  - Set capacity and refill rate
  - Initialize tokens to capacity (full bucket)
  - Initialize RNG seed
- [ ] Implement `token_bucket_refill()`:
  - Calculate elapsed time since last refill
  - Compute tokens to add: `delta_tokens = refill_rate * elapsed_ms`
  - Add stochastic variance using LCG:
    ```c
    uint32_t variance = lcg_next(&rng_seed) % 10;  /* ±10% variance */
    delta_tokens += (delta_tokens * variance) / 100;
    ```
  - Clamp to capacity
- [ ] Implement `token_bucket_consume()`:
  - Refill bucket first
  - Check if requested tokens available
  - If yes: subtract tokens, return success
  - If no: return failure (rate limited)

**Success criteria**: Token bucket correctly limits rate under stress test

---

### Task 2.4.2: Integrate token bucket with capabilities
**File**: `kernel/capability_v2.c`
**Estimated time**: 2 hours

**Subtasks**:
- [ ] Add token bucket to `struct capability_v2`:
  - Initialize in `capv2_alloc()`
  - Configure based on capability type and quota
- [ ] Modify `capv2_check_rights()` to check token bucket:
  ```c
  /* Check rate limit before checking rights */
  if (!token_bucket_consume(&cap->rate_limit, 1)) {
      return 0;  /* Rate limited - no rights granted */
  }
  ```
- [ ] Add syscall for querying token bucket status:
  - `sys_capv2_get_tokens(cap_slot, &tokens_remaining)`
  - Useful for applications to adapt behavior
- [ ] Add pedagogical example showing rate limiting in action

**Success criteria**: Capabilities correctly rate-limited under heavy access

---

## Phase 2.5: Cap'n Proto Integration (Days 11-13)

### Task 2.5.1: Design capability serialization schema
**File**: `proto/capability_v2.capnp` (if using real Cap'n Proto) or `include/capnp_simple.h` (simplified)
**Estimated time**: 3 hours

**Decision point**: Real Cap'n Proto vs. simplified zero-copy serialization?
- **Option A**: Full Cap'n Proto integration (requires external library)
- **Option B**: Simplified zero-copy serialization inspired by Cap'n Proto

**Recommended**: Option B (simplified) for kernel simplicity

**Subtasks** (Option B):
- [ ] Define simplified message format:
  ```c
  struct capnp_message_v2 {
      uint32_t message_type;   /* Schema ID */
      uint32_t cap_count;      /* Number of capabilities */
      uint32_t data_offset;    /* Offset to payload data */
      uint32_t data_size;      /* Size of payload */
      /* Followed by: */
      /* uint32_t cap_slots[cap_count] - Capability slot indices */
      /* uint8_t data[data_size] - Payload bytes */
  };
  ```
- [ ] Define message builder API:
  - `capnp_msg_builder_init()`
  - `capnp_msg_builder_add_cap(cap_slot)`
  - `capnp_msg_builder_add_data(ptr, size)`
  - `capnp_msg_builder_finalize()` - Return pointer to serialized message
- [ ] Define message reader API:
  - `capnp_msg_reader_init(buffer)`
  - `capnp_msg_reader_get_cap(index)` - Extract capability slot
  - `capnp_msg_reader_get_data()` - Get payload pointer (zero-copy!)

**Success criteria**: Messages can be serialized/deserialized without copies

---

### Task 2.5.2: Implement zero-copy IPC with capabilities
**File**: `kernel/ipc_v2.c`
**Estimated time**: 4 hours

**Subtasks**:
- [ ] Extend existing IPC system to support `capnp_message_v2`:
  - Reuse existing `exo_ipc` infrastructure
  - Add capability transfer semantics
- [ ] Implement `ipc_send_with_caps()`:
  ```c
  int ipc_send_with_caps(
      uint32_t recipient_pid,
      struct capnp_message_v2 *msg
  ) {
      /* Validate all capability slots in message */
      for (int i = 0; i < msg->cap_count; i++) {
          if (!capv2_check_rights(msg->cap_slots[i], CAP_RIGHT_GRANT)) {
              return -EPERM;  /* Sender doesn't have grant rights */
          }
      }

      /* Transfer capabilities to recipient */
      for (int i = 0; i < msg->cap_count; i++) {
          capv2_grant(msg->cap_slots[i], recipient_pid);
      }

      /* Send message via existing IPC (zero-copy) */
      return exo_ipc_send(recipient_pid, msg, sizeof(*msg) + msg->data_size);
  }
  ```
- [ ] Implement `ipc_recv_with_caps()`:
  - Receive message
  - Map received capability slots into recipient's namespace
  - Return message pointer (zero-copy)
- [ ] Add security checks:
  - Validate sender has permission to send to recipient
  - Validate capability delegation is allowed
  - Prevent capability forgery

**Success criteria**: IPC can transfer capabilities without kernel copies

---

### Task 2.5.3: Add pedagogical examples for IPC
**File**: `kernel/capability_v2.c` (in DEBUG mode)
**Estimated time**: 2 hours

**Subtasks**:
- [ ] Example 1: Simple capability transfer
  - Process A creates capability
  - Process A sends to Process B via IPC
  - Process B uses capability
  - Verify rights preserved
- [ ] Example 2: Derived capability transfer
  - Process A creates capability with full rights
  - Process A derives child capability with reduced rights
  - Process A sends child to Process B
  - Process B attempts to use full rights (fails)
  - Process B uses allowed rights (succeeds)
- [ ] Example 3: Time-degrading capability
  - Create capability with time-decay formula
  - Transfer to another process
  - Wait for decay period
  - Verify rights reduced over time

**Success criteria**: Examples demonstrate capability transfer, derivation, and dynamic rights

---

## Phase 2.6: Testing & Documentation (Days 14)

### Task 2.6.1: Write comprehensive unit tests
**File**: `tests/c17/unit/test_capability_v2.c`
**Estimated time**: 4 hours

**Subtasks**:
- [ ] Test capability allocation/deallocation:
  - Allocate all slots, verify table full
  - Free all slots, verify free list correct
  - Allocation after free reuses slots
- [ ] Test capability grant/revoke:
  - Grant creates new reference
  - Revoke decrements refcount
  - Free only when refcount hits 0
- [ ] Test capability derivation:
  - Derived cap has reduced quota
  - Derived cap cannot exceed parent
  - Revoking parent revokes children
- [ ] Test lambda formulas:
  - Time-decay formula reduces rights over time
  - User-based formula grants different rights per user
  - Quota-based formula revokes when tokens exhausted
- [ ] Test token buckets:
  - Bucket refills at correct rate
  - Stochastic variance adds randomness
  - Bucket correctly rate-limits access
- [ ] Test IPC with capabilities:
  - Capability transfer preserves rights
  - Derived capabilities work across IPC
  - Revocation works after IPC transfer

**Success criteria**: All tests pass with 100% code coverage (if measurable)

---

### Task 2.6.2: Write capability system tutorial
**File**: `docs/CAPABILITY_V2_TUTORIAL.md`
**Estimated time**: 2 hours

**Subtasks**:
- [ ] Introduction: Why capabilities?
  - Compare to ACLs (Access Control Lists)
  - Capabilities = unforgeable tokens
  - PDAC extends with resource quotas and dynamic rights
- [ ] Section 1: Basic operations
  - Allocating capabilities
  - Granting to other processes
  - Revoking capabilities
  - Code examples for each
- [ ] Section 2: Resource quotas
  - Using octonion resource vectors
  - Deriving capabilities with reduced quotas
  - How quota enforcement works
- [ ] Section 3: Dynamic rights with lambda formulas
  - Time-based capabilities
  - User-based capabilities
  - Quota-based capabilities
  - Composing formulas
- [ ] Section 4: IPC with capabilities
  - Zero-copy message passing
  - Transferring capabilities between processes
  - Security considerations
- [ ] Comparison to real-world systems:
  - seL4 capabilities (what we borrowed)
  - Cap'n Proto (zero-copy inspiration)
  - Google Borg resource quotas

**Success criteria**: Tutorial is accessible to OS course students (undergraduate level)

---

### Task 2.6.3: Update PDAC framework documentation
**File**: `PDAC_UNIFIED_FRAMEWORK.md`
**Estimated time**: 1 hour

**Subtasks**:
- [ ] Mark Phase 2 as complete
- [ ] Add links to Phase 2 implementation files
- [ ] Add performance measurements:
  - Capability allocation time
  - Rights checking latency
  - IPC throughput with capabilities
- [ ] Add lessons learned section:
  - What worked well
  - What was challenging
  - Design decisions and trade-offs

**Success criteria**: Documentation reflects implemented state

---

## Success Metrics for Phase 2

### Functional Requirements
- ✅ Capability table supports 4096 slots
- ✅ All basic operations work: alloc, free, grant, revoke, derive
- ✅ Lambda formulas correctly compute dynamic rights
- ✅ Token buckets correctly rate-limit access
- ✅ IPC can transfer capabilities without copies
- ✅ Resource vectors integrated (8D quota enforcement)

### Performance Requirements
- ✅ Capability allocation: < 1 microsecond (amortized)
- ✅ Rights checking: < 100 nanoseconds (without formula)
- ✅ Rights checking with formula: < 500 nanoseconds
- ✅ IPC with capabilities: < 10% overhead vs. IPC without caps

### Code Quality Requirements
- ✅ Zero compiler warnings with -Werror
- ✅ All public APIs documented with examples
- ✅ Unit test coverage > 80%
- ✅ Pedagogical examples demonstrate key concepts

### Pedagogical Requirements
- ✅ Tutorial explains why capabilities matter
- ✅ Examples show integration with resource vectors
- ✅ Comparison to seL4 and Cap'n Proto included
- ✅ Educational value clear for OS students

---

## Phase 2 Task Dependency Graph

```
Task 2.1.1 (core struct)
    ↓
Task 2.1.2 (API design) ──→ Task 2.1.3 (types/rights)
    ↓
Task 2.2.1 (table init) ──→ Task 2.2.2 (core ops) ──→ Task 2.2.3 (locking)
    ↓
Task 2.3.1 (formula design) ──→ Task 2.3.2 (formula impl) ──→ Task 2.3.3 (integration)
    ↓
Task 2.4.1 (token bucket) ──→ Task 2.4.2 (integration)
    ↓
Task 2.5.1 (serialization) ──→ Task 2.5.2 (IPC) ──→ Task 2.5.3 (examples)
    ↓
Task 2.6.1 (tests) ──→ Task 2.6.2 (tutorial) ──→ Task 2.6.3 (docs update)
```

---

## Estimated Total Time

| Phase | Tasks | Estimated Hours |
|-------|-------|-----------------|
| 2.1 (Design) | 3 tasks | 6 hours |
| 2.2 (Core Implementation) | 3 tasks | 9 hours |
| 2.3 (Lambda Formulas) | 3 tasks | 9 hours |
| 2.4 (Token Buckets) | 2 tasks | 5 hours |
| 2.5 (Cap'n Proto) | 3 tasks | 9 hours |
| 2.6 (Testing & Docs) | 3 tasks | 7 hours |
| **Total** | **17 tasks** | **45 hours** |

**Timeline**: ~2 weeks at 4-6 hours/day (or 1 week at 8-10 hours/day)

---

## Next Phase Preview: Phase 3 - Stochastic Scheduler

After Phase 2 completes, Phase 3 will integrate:
- Linear Congruential Generator (LCG) for randomness
- Lottery scheduling with octonion-weighted tickets
- Hybrid lottery + Beatty scheduler (80% lottery, 20% Beatty)
- Token bucket integration with scheduler quotas

This builds on Phase 2's token buckets and Phase 1's resource vectors to create a **provably fair, stochastically balanced, multidimensional scheduler** - a novel contribution to OS scheduling theory!

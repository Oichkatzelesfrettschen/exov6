# Lambda Capability User Guide

## Overview

The **Lambda Capability Engine** (lambda_cap) is FeuerBird's sophisticated capability system that unifies functional programming, process algebra, and exokernel security. It provides:

- **Linear capability semantics**: Capabilities can be used exactly once, preventing use-after-free
- **Pi-calculus process algebra**: Concurrent processes communicate through named channels
- **S-expression lambda calculus**: Functional evaluation with higher-order functions
- **Superforce energy accounting**: Resource management based on quantum field theory
- **Octonion state representation**: 8-dimensional mathematical state vectors

Lambda capabilities integrate tightly with FeuerBird's capability table, ensuring that all operations are tracked, authenticated, and can be revoked atomically.

---

## When to Use Lambda_Cap

Lambda_cap is ideal when you need:

1. **Secure concurrent communication**: Multiple processes need to exchange messages safely
2. **Resource-bounded execution**: Functions must run within energy/fuel limits
3. **Functional composition**: Combining processes mathematically (parallel and sequential)
4. **Revokable access**: Single operation to invalidate all capabilities and channels
5. **Type-safe channel usage**: Compile-time awareness of single-use channel semantics

### Comparison with Regular Capabilities

| Feature | Regular Capability | Lambda_Cap |
|---------|-------------------|-----------|
| **Reusability** | Can be used multiple times | Single-use (affine) |
| **Communication** | Individual operations | Pi-calculus channels |
| **Computation** | No computation model | S-expression evaluation |
| **Energy tracking** | Basic accounting | Superforce quantum units |
| **Composition** | Not supported | Parallel & sequential |

---

## Core Concepts

### 1. What is a Lambda Capability?

A **lambda capability** is a unified capability-process-function object:

```c
struct lambda_cap {
    cap_id_t cap_id;                  // Capability table ID

    /* Process algebra */
    struct pi_channel **channels;     // Communication channels

    /* Functional computation */
    struct s_expr *expression;        // S-expression to evaluate
    void (*native_fn)(void *);        // Native function pointer

    /* Energy budget */
    uint64_t energy_quanta;           // Planck-scale energy units
    uint32_t fuel;                    // Execution cycles

    /* State representation */
    octonion_t state_vector;          // 8-dimensional state

    /* Linear type semantics */
    bool consumed;                    // Used exactly once
};
```

### 2. Affine Types (Single-Use)

A lambda capability can only be used once. After use, it's marked `consumed` and cannot be used again:

```c
int result = lambda_cap_use(lc, 500);  // Use with 500 fuel

if (result == LAMBDA_CAP_SUCCESS) {
    // Capability consumed, cannot use again
    int result2 = lambda_cap_use(lc, 100);  // ERROR: consumed
}
```

This **prevents use-after-free vulnerabilities** automatically at the language/runtime level.

### 3. Pi-Calculus Channels

Processes communicate through **pi-calculus channels**—named endpoints with separate send and receive capabilities:

```c
struct pi_channel {
    cap_id_t send_cap;                // Write-only capability
    cap_id_t recv_cap;                // Read-only capability

    bool used_send;                   // Affine: sent exactly once
    bool used_recv;                   // Affine: received exactly once
};
```

Each direction is independently affine:
- **Send**: `P⟨expr⟩` — transmit expression through channel
- **Receive**: `x(expr)` — receive and bind to variable

### 4. Superforce Energy Accounting

Energy is tracked in **Planck-scale quantum units** (Superforce constant = c⁴/G):

```c
/* Allocate capability with 1000 energy quanta */
struct lambda_cap *lc = lambda_cap_create(my_fn, NULL, cap);

/* Check available energy */
uint64_t available = lambda_cap_available_energy(lc);

/* Transfer energy between capabilities */
lambda_cap_transfer_energy(source, dest, 100);  // Move 100 quanta
```

Energy deduction prevents **resource exhaustion attacks** by enforcing hard limits on execution.

### 5. Octonion State Vectors

Capabilities maintain **8-dimensional state** using octonions (generalization of complex numbers):

```c
/* State vector: (e0, e1, e2, e3, e4, e5, e6, e7) */
octonion_t state = lc->state_vector;

/* Non-associative composition (unique to octonions) */
octonion_t result = octonion_mul(state1, state2);
// Note: (a × b) × c ≠ a × (b × c)
```

This enables mathematical composition of process states with **non-commutative semantics**.

---

## API Reference

### Creating Capabilities

#### `lambda_cap_create()`
Allocate a new lambda capability with optional native function.

```c
struct lambda_cap *lc = lambda_cap_create(
    void (*native_fn)(void *),        // Optional: native function pointer
    struct s_expr *expr,              // Optional: S-expression to evaluate
    exo_cap cap                       // Capability granting ownership
);

// Returns: pointer to lambda_cap, or NULL on error
// Allocates: capability table entry (CAP_TYPE_CRYPTOKEY)
// Energy: 1000 quanta initial budget
```

**Example**:
```c
void handler(void *env) {
    cprintf("Lambda called\n");
}

exo_cap owner_cap = cap_new(0, EXO_RIGHT_RWX, myproc()->pid);
struct lambda_cap *lc = lambda_cap_create(handler, NULL, owner_cap);
```

#### `lambda_cap_create_channel()`
Create a pi-calculus channel pair between two capabilities.

```c
int lambda_cap_create_channel(
    struct lambda_cap *sender,        // Sender capability
    struct lambda_cap *receiver,      // Receiver capability
    struct pi_channel **channel_out   // Output: new channel
);

// Returns: 0 on success, negative on error
// Creates: separate send and receive capabilities
```

**Example**:
```c
struct pi_channel *ch;
if (lambda_cap_create_channel(producer, consumer, &ch) == 0) {
    // Channel created: ch->send_cap and ch->recv_cap
}
```

### Using Capabilities

#### `lambda_cap_use()`
Execute a lambda capability with fuel budget.

```c
int lambda_cap_use(
    struct lambda_cap *lc,            // Capability to execute
    uint32_t fuel                     // Fuel budget for execution
);

// Returns:
//   0  = LAMBDA_CAP_SUCCESS
//   -1 = NULL capability
//   -2 = Already consumed (affine violation)
//   -3 = Invalid capability (revoked)
//   -4 = Insufficient energy (superforce limit)
```

**Example**:
```c
if (lambda_cap_use(lc, 500) == 0) {
    cprintf("Executed successfully\n");
} else {
    cprintf("Execution failed\n");
}

// Cannot use again:
lambda_cap_use(lc, 100);  // Returns -2 (consumed)
```

#### `lambda_cap_channel_send()`
Send S-expression through a channel.

```c
int lambda_cap_channel_send(
    struct pi_channel *ch,            // Channel to send through
    struct s_expr *expr               // Expression to transmit
);

// Returns: 0 on success, negative on error
// Behavior: Affine — can only send once per channel
// Effect: Receiver can receive the transmitted value
```

**Example**:
```c
struct s_expr *msg = s_expr_integer(42);
if (lambda_cap_channel_send(ch, msg) == 0) {
    cprintf("Message sent\n");
} else if (result == -2) {
    cprintf("Channel already used for send\n");
}
```

#### `lambda_cap_channel_recv()`
Receive S-expression from a channel.

```c
int lambda_cap_channel_recv(
    struct pi_channel *ch,            // Channel to receive from
    struct s_expr **expr_out          // Output: received expression
);

// Returns: 0 on success, negative on error
// Behavior: Affine — can only receive once per channel
// Effect: Blocks until message available (if queue empty)
```

**Example**:
```c
struct s_expr *result;
if (lambda_cap_channel_recv(ch, &result) == 0) {
    cprintf("Received: ");
    s_expr_print(result);
}
```

### Energy Management

#### `lambda_cap_available_energy()`
Query remaining energy budget.

```c
uint64_t lambda_cap_available_energy(struct lambda_cap *lc);

// Returns: Remaining energy quanta
// Does NOT consume energy
```

#### `lambda_cap_transfer_energy()`
Transfer energy from one capability to another.

```c
int lambda_cap_transfer_energy(
    struct lambda_cap *src,           // Source capability
    struct lambda_cap *dst,           // Destination capability
    uint64_t amount                   // Energy quanta to transfer
);

// Returns: 0 on success, negative on error
// Effect: Atomic transfer (safe for concurrent access)
// Energy conservation: src_before + dst_before = src_after + dst_after
```

**Example**:
```c
uint64_t available = lambda_cap_available_energy(lc1);
if (available > 100) {
    lambda_cap_transfer_energy(lc1, lc2, 100);
}
```

### Composition

#### `lambda_cap_compose_parallel()`
Create parallel composition (P | Q).

```c
int lambda_cap_compose_parallel(
    struct lambda_cap *left,          // First process
    struct lambda_cap *right,         // Second process
    struct lambda_cap **result        // Output: composed capability
);

// Returns: 0 on success, negative on error
// Energy: parallel_energy = left_energy + right_energy
// State: state_parallel = state_left × state_right (octonion)
```

**Example**:
```c
struct lambda_cap *parallel;
if (lambda_cap_compose_parallel(proc1, proc2, &parallel) == 0) {
    // parallel can be used with combined energy budget
    lambda_cap_use(parallel, 1000);
}
```

#### `lambda_cap_compose_sequential()`
Create sequential composition (P ; Q).

```c
int lambda_cap_compose_sequential(
    struct lambda_cap *first,         // First process (runs first)
    struct lambda_cap *second,        // Second process (runs second)
    struct lambda_cap **result        // Output: composed capability
);

// Returns: 0 on success, negative on error
// Energy: sequential_energy = min(first_energy, second_energy)
// Order: first executes completely, then second
```

**Example**:
```c
struct lambda_cap *sequence;
if (lambda_cap_compose_sequential(setup, main_work, &sequence) == 0) {
    // First setup runs, then main_work (with bottleneck energy)
    lambda_cap_use(sequence, 500);
}
```

### Revocation

#### `lambda_cap_revoke()`
Invalidate a capability and all its channels.

```c
int lambda_cap_revoke(struct lambda_cap *lc);

// Returns: 0 on success, negative on error
// Effect:
//   1. Capability table epoch bumped (invalidates all old IDs)
//   2. All send/receive capabilities revoked
//   3. Energy reset to 0
//   4. Capability marked consumed
// Consequence: All outstanding references become invalid immediately
```

**Example**:
```c
if (lambda_cap_revoke(lc) == 0) {
    // All references to lc and its channels now invalid
    // Other processes holding capabilities get LAMBDA_CAP_ERROR_INVALID_CAP
}
```

---

## Pi-Calculus Process Algebra

### Process Notation

Lambda_cap implements **Milner's π-calculus** process algebra:

| Notation | Meaning | Lambda_cap |
|----------|---------|-----------|
| `P ⟨expr⟩.Q` | Send expr, then do Q | `lambda_cap_channel_send()` + continue |
| `x(y).P` | Receive on x, bind to y, then P | `lambda_cap_channel_recv()` + continue |
| `νx.(P)` | Restrict channel x to P | `lambda_cap_create_channel()` scope |
| `P \| Q` | P and Q run in parallel | `lambda_cap_compose_parallel()` |
| `P;Q` | P then Q sequentially | `lambda_cap_compose_sequential()` |

### Example: Producer-Consumer Pattern

```c
/* Producer: sends integers 0..99 through channel */
void producer(void *env) {
    struct pi_channel *ch = (struct pi_channel *)env;

    for (int i = 0; i < 100; i++) {
        struct s_expr *msg = s_expr_integer(i);
        lambda_cap_channel_send(ch, msg);
    }
    // Channel send capability now consumed
}

/* Consumer: receives integers and processes them */
void consumer(void *env) {
    struct pi_channel *ch = (struct pi_channel *)env;
    struct s_expr *msg;

    for (int i = 0; i < 100; i++) {
        if (lambda_cap_channel_recv(ch, &msg) == 0) {
            // Process msg...
        }
    }
}

/* Main: create channel and compose */
exo_cap prod_cap = cap_new(0, EXO_RIGHT_RWX, myproc()->pid);
exo_cap cons_cap = cap_new(0, EXO_RIGHT_RWX, myproc()->pid);

struct lambda_cap *producer_lc = lambda_cap_create(producer, NULL, prod_cap);
struct lambda_cap *consumer_lc = lambda_cap_create(consumer, NULL, cons_cap);

struct pi_channel *ch;
lambda_cap_create_channel(producer_lc, consumer_lc, &ch);

/* Parallel execution */
struct lambda_cap *parallel;
lambda_cap_compose_parallel(producer_lc, consumer_lc, &parallel);
lambda_cap_use(parallel, 5000);  // 5000 fuel total
```

---

## S-Expression Lambda Calculus

### Syntax

Lambda_cap supports **lambda calculus** through S-expressions:

```
expr := atom
      | (lambda x body)        ; λx.body
      | (expr expr)            ; function application
      | number
      | string
```

### Building Expressions

```c
/* Atom */
struct s_expr *atom = s_expr_atom("foo");

/* Integer */
struct s_expr *num = s_expr_integer(42);

/* String */
struct s_expr *str = s_expr_string("hello");

/* Lambda abstraction: λx.(x + 1) */
struct s_expr *param = s_expr_atom("x");
struct s_expr *body = s_expr_cons(
    s_expr_atom("+"),
    s_expr_cons(param, s_expr_cons(s_expr_integer(1), NULL))
);
struct s_expr *lambda = s_expr_lambda(param, body);

/* Function application: ((λx.x) 5) */
struct s_expr *applied = s_expr_cons(
    lambda,
    s_expr_integer(5)
);
```

### Evaluation

```c
/* Evaluate expression in environment */
struct s_expr *result;
struct s_expr_env *env = s_expr_env_create();
s_expr_eval(lambda, env, &result);

/* Print result */
s_expr_print(result);  // Output representation

/* Free environment */
s_expr_env_free(env);
```

### Example: Simple Calculator

```c
/* Create expression: (+ 2 3) */
struct s_expr *expr = s_expr_cons(
    s_expr_atom("+"),
    s_expr_cons(
        s_expr_integer(2),
        s_expr_cons(s_expr_integer(3), NULL)
    )
);

/* Evaluate */
struct s_expr *result;
struct s_expr_env *env = s_expr_env_create();
if (s_expr_eval(expr, env, &result) == 0) {
    // result now contains 5
    s_expr_print(result);  // "5"
}
```

---

## Energy and Resource Management

### Understanding Superforce Energy

The Superforce constant represents the fundamental energy scale (c⁴/G in physics):

```
SUPERFORCE ≈ 1.21 × 10⁴⁴ Newtons
```

In lambda_cap, energy is quantized:

```c
struct lambda_cap *lc = lambda_cap_create(fn, NULL, cap);
// Initial: energy_quanta = 1000 (in Planck units)
//          fuel = 1000 (execution cycles)

lambda_cap_use(lc, 500);  // Consume 500 fuel
// Now: fuel remaining = 500
```

### Energy Budgeting

Allocate energy proportional to task complexity:

```c
/* Lightweight operation: 100 fuel */
lambda_cap_use(quick_task, 100);

/* Medium task: 1000 fuel */
lambda_cap_use(normal_task, 1000);

/* Intensive computation: 10000 fuel */
lambda_cap_use(heavy_task, 10000);
```

### Energy Transfer Pattern

```c
void load_balance(struct lambda_cap *overloaded,
                  struct lambda_cap *underused) {
    uint64_t available = lambda_cap_available_energy(overloaded);

    /* Transfer 50% of excess energy */
    if (available > 2000) {
        uint64_t transfer = (available - 1000) / 2;
        lambda_cap_transfer_energy(overloaded, underused, transfer);
    }
}
```

---

## Type Safety and Linear Logic

### Affine Type System

Lambda capabilities enforce **affine types** (use at most once):

```c
struct lambda_cap *lc = lambda_cap_create(fn, NULL, cap);

/* First use: succeeds */
int result1 = lambda_cap_use(lc, 500);
assert(result1 == 0);

/* Second use: fails (already consumed) */
int result2 = lambda_cap_use(lc, 500);
assert(result2 == LAMBDA_CAP_ERROR_CONSUMED);

/* This prevents use-after-free at the type level */
```

### Channel Affinity

Each channel endpoint can be used exactly once:

```c
struct pi_channel *ch;
lambda_cap_create_channel(sender, receiver, &ch);

/* First send: succeeds */
lambda_cap_channel_send(ch, msg1);  // ch->used_send = true

/* Second send: fails */
lambda_cap_channel_send(ch, msg2);  // ERROR: already used

/* First receive: succeeds */
lambda_cap_channel_recv(ch, &result);  // ch->used_recv = true

/* Second receive: fails */
lambda_cap_channel_recv(ch, &result);  // ERROR: already used
```

This **prevents concurrent access violations** automatically.

---

## Formal Verification Foundation

Lambda_cap is designed to be formally verifiable in **Rocq Prover** using:

1. **Linear Type Theory**: Affine types ensure single-use properties
2. **Process Algebra**: Pi-calculus gives formal semantics for channels
3. **Energy Accounting**: Superforce energy provides termination guarantees
4. **Capability Security**: Epoch-based revocation has proven security properties

### Verifiable Properties

```
Property 1: Linearity
  Use-after-free is impossible: once consumed, use fails

Property 2: Channel Safety
  Capacity violations impossible: each endpoint used exactly once

Property 3: Energy Conservation
  Energy is conserved: total_before = total_after on transfer

Property 4: Revocation
  Revocation atomic: epoch change invalidates all old IDs instantly
```

---

## Integration with Exokernel

Lambda capabilities integrate with FeuerBird's exokernel layer:

### Capability Table Integration

```c
/* Lambda capabilities stored in capability table */
cap_id_t id = lambda_cap_create(...)->cap_id;

/* Lookup by ID */
struct cap_entry entry;
cap_table_lookup(id, &entry);

/* Revocation bumps epoch */
lambda_cap_revoke(lc);  /* Invalidates all old IDs */
```

### Resource Accounting

```c
/* Energy tracked in exokernel accounting */
struct exo_account *account = exo_account_create(myproc()->pid);
exo_account_deduct_energy(account, energy_used);
exo_account_add_fuel_consumed(account, fuel_used);
```

### Process Context

```c
/* Lambda capabilities scoped to process */
struct proc *p = myproc();
struct lambda_cap *lc = lambda_cap_create(fn, NULL, cap);
// Owner is p->pid (tracked in capability table)
```

---

## Common Patterns

### 1. Simple Function Execution

```c
void my_task(void *env) {
    cprintf("Task running\n");
}

exo_cap cap = cap_new(0, EXO_RIGHT_RWX, myproc()->pid);
struct lambda_cap *lc = lambda_cap_create(my_task, NULL, cap);
lambda_cap_use(lc, 100);
```

### 2. Message Pipeline

```c
/* Create pipeline: producer -> filter -> consumer */

struct lambda_cap *prod, *filt, *cons;
struct pi_channel *ch1, *ch2;

lambda_cap_create_channel(prod, filt, &ch1);
lambda_cap_create_channel(filt, cons, &ch2);

struct lambda_cap *pipeline;
lambda_cap_compose_parallel(prod,
    lambda_cap_compose_parallel(filt, cons, &temp),
    &pipeline);

lambda_cap_use(pipeline, 5000);
```

### 3. Resource-Bounded Work Queue

```c
struct lambda_cap *work_item[100];
for (int i = 0; i < 100; i++) {
    work_item[i] = lambda_cap_create(worker, NULL, cap);
}

/* Run with energy budget */
for (int i = 0; i < 100; i++) {
    uint64_t energy = lambda_cap_available_energy(work_item[i]);
    if (energy > 0) {
        lambda_cap_use(work_item[i], 100);
    }
}
```

### 4. Dynamic Capability Delegation

```c
struct lambda_cap *delegate_work(struct lambda_cap *parent_cap) {
    /* Create child capability */
    struct lambda_cap *child = lambda_cap_create(worker_fn, NULL, cap);

    /* Transfer energy from parent to child */
    uint64_t half = lambda_cap_available_energy(parent_cap) / 2;
    lambda_cap_transfer_energy(parent_cap, child, half);

    return child;
}
```

---

## Troubleshooting

### Problem: LAMBDA_CAP_ERROR_CONSUMED

**Cause**: Trying to use a capability twice

```c
lambda_cap_use(lc, 100);   // OK
lambda_cap_use(lc, 100);   // ERROR: consumed
```

**Solution**: Create a new capability or use composition

```c
struct lambda_cap *lc1 = lambda_cap_create(fn, NULL, cap);
struct lambda_cap *lc2 = lambda_cap_create(fn, NULL, cap);
lambda_cap_use(lc1, 100);
lambda_cap_use(lc2, 100);  // OK
```

### Problem: LAMBDA_CAP_ERROR_INSUFFICIENT_ENERGY

**Cause**: Requesting more fuel than available energy

```c
lambda_cap_use(lc, 10000);  // ERROR: only 1000 quanta available
```

**Solution**: Check available energy before use

```c
uint64_t available = lambda_cap_available_energy(lc);
if (available > 5000) {
    lambda_cap_use(lc, 5000);
} else {
    lambda_cap_transfer_energy(other, lc, 5000);
    lambda_cap_use(lc, 5000);
}
```

### Problem: Channel Operations Fail

**Cause**: Channel endpoints already used (affine violation)

```c
lambda_cap_channel_send(ch, msg1);  // OK
lambda_cap_channel_send(ch, msg2);  // ERROR: already sent
```

**Solution**: Create separate channels for multiple messages

```c
struct pi_channel *ch1, *ch2;
lambda_cap_create_channel(sender, receiver, &ch1);
lambda_cap_create_channel(sender, receiver, &ch2);
lambda_cap_channel_send(ch1, msg1);  // OK
lambda_cap_channel_send(ch2, msg2);  // OK
```

---

## Further Reading

- **Pi-Calculus**: Milner, R. *The Polyadic π-Calculus: A Tutorial* (1991)
- **Linear Logic**: Girard, J. *Linear Logic* (1987)
- **Superforce Energy**: Pais, A. *The Genius of Science* (2000)
- **Octonion Algebra**: Baez, J. *The Octonions* (2002)

---

## See Also

- `docs/ARCHITECTURE.md` - System architecture overview
- `include/lambda_cap.h` - API header with complete function signatures
- `kernel/lambda_cap.c` - Implementation source code (1475+ lines)
- `docs/FORMAL_VERIFICATION.md` - Rocq proof framework

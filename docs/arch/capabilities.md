# Capability Lifecycle & PDAC System

This document describes the **PDAC (Probabilistic DAG Algebra with Capabilities) System V2**, the core security mechanism of the Phoenix Exokernel. It unifies seL4-style capabilities with flexible resource vectors and lambda-calculus-based rights.

## 1. Architecture

The capability system is implemented as a global, fixed-size table in the kernel (`kernel/capability_v2.c`).

*   **Storage**: A fixed-size array of `4096` capability slots.
*   **Allocation**: O(1) allocation using a free-list.
*   **Concurrency**: Fine-grained locking with per-capability spinlocks (`qspinlock`).
*   **Safety**:
    *   **Generation Counters**: Prevent "ABA problems" (use-after-free) by invalidating weak references when a slot is reused.
    *   **Reference Counting**: Ensures capabilities are only freed when no longer in use.

## 2. Capability Lifecycle

The lifecycle of a capability follows a strict state machine:

### 2.1. Creation (`Alloc`)
*   **Operation**: `capv2_alloc(resource, type, rights, quota)`
*   **State**: Refcount = 1.
*   **Owner**: The creating process.
*   **Quota**: Initialized with an 8-dimensional resource vector (CPU, Mem, I/O, etc.).

### 2.2. Delegation (`Grant`)
*   **Operation**: `capv2_grant(cap, recipient_pid, rights)`
*   **Invariant**: **Rights Attenuation**. The recipient's rights must be a subset of the granter's rights. Never escalation.
*   **Mechanism**: Creates a new capability slot for the recipient, pointing to the same underlying resource but with potentially fewer rights.
*   **Tree**: Maintains a parent/child relationship for revocation.

### 2.3. Derivation (`Derive`)
*   **Operation**: `capv2_derive(parent, quota, rights)`
*   **Purpose**: Create a weaker capability (less quota) from a parent.
*   **PDAC Innovation**: Subdivides the 8D resource vector.
    *   Example: Parent has 10MB Memory. Child gets 2MB. Parent remaining = 8MB.

### 2.4. Revocation (`Revoke`)
*   **Operation**: `capv2_revoke(cap)`
*   **Recursive**: Revokes the capability and **all** its children (recursively traversing the derivation tree).
*   **Refcount**: Decrements refcounts, potentially freeing slots.

### 2.5. Destruction (`Free`)
*   **Operation**: `capv2_free(cap)`
*   **Condition**: Can only occur when `refcount == 0`.
*   **Cleanup**: Zeroes out the slot to prevent data leaks and returns it to the free list.

## 3. PDAC Features

### 3.1. 8D Resource Vectors
Instead of a single "size", capabilities carry an 8-dimensional quota vector:
1.  CPU Time
2.  Memory Usage
3.  I/O Bandwidth
4.  Network Bandwidth
5.  GPU Time
6.  Disk Quota
7.  IRQ Count
8.  Capability Count

### 3.2. Lambda Rights
Rights can be dynamic, computed by a function (`rights_fn`) at runtime.
*   **Use Cases**: Time-based expiry, usage-based revocation, state-dependent access.
*   **Formula**: `effective_rights = static_rights & formula(cap, data)`

### 3.3. Rate Limiting
Capabilities support Token Bucket rate limiting.
*   **Check**: `capv2_check_rights_ratelimited`
*   **Enforcement**: Consumes tokens on access; denies access if bucket empty.

# Capability Security Model

## Overview

FeuerBird uses unforgeable capabilities as the foundation for all access control decisions. Every resource access requires a valid capability.

## Capability Structure

```c
typedef struct capability {
    cap_id_t id;           // Unique identifier (16-bit)
    cap_type_t type;       // Resource type
    uint32_t permissions;  // Access rights
    uint64_t auth_token;   // Authentication hash
    void *resource;        // Resource pointer
    uint32_t ref_count;    // Reference counting
} capability_t;
```

## Capability Types

### Memory Capabilities
- Physical page access
- Virtual memory regions
- DMA buffers
- Shared memory segments

### CPU Capabilities
- Time slice allocation
- Priority levels
- CPU affinity
- Interrupt handling

### I/O Capabilities
- Disk block access
- Network interfaces
- Device registers
- Port I/O

### IPC Capabilities
- Message channels
- Shared queues
- Semaphores
- Event notifications

## Authentication Mechanism

### Current: FNV-1a Hash
```c
uint64_t cap_authenticate(cap_id_t id, void *resource) {
    uint64_t hash = FNV_OFFSET_BASIS;
    hash = fnv1a_hash(hash, &id, sizeof(id));
    hash = fnv1a_hash(hash, resource, sizeof(void*));
    return hash;
}
```

### Future: HMAC-SHA256
```c
// Planned upgrade for stronger security
uint256_t cap_authenticate_hmac(cap_id_t id, void *resource) {
    return hmac_sha256(secret_key, id, resource);
}
```

## Capability Operations

### Creation
```c
cap_id_t cap = cap_create(CAP_TYPE_MEMORY, resource, permissions);
```

### Validation
```c
if (cap_validate(cap, &entry) == VALIDATION_SUCCESS) {
    // Access granted
}
```

### Delegation
```c
cap_id_t new_cap = cap_delegate(cap, target_process, reduced_perms);
```

### Revocation
```c
cap_revoke(cap);  // Immediate revocation
cap_revoke_tree(cap);  // Revoke all derived capabilities
```

## Reference Counting

### Increment on:
- Capability creation
- Capability copy
- Cross-zone transfer

### Decrement on:
- Capability drop
- Process termination
- Explicit release

### Cleanup:
```c
if (atomic_dec(&cap->ref_count) == 0) {
    cap_destroy(cap);
}
```

## Capability Table Management

### Table Structure
```c
#define CAP_TABLE_SIZE 65536

static struct {
    capability_t entries[CAP_TABLE_SIZE];
    uint32_t free_list;
    spinlock_t lock;
} cap_table;
```

### Allocation Strategy
1. Check free list
2. Linear search if empty
3. Expand table if full
4. Return CAP_INVALID on failure

## Security Properties

### Unforgeability
- Cryptographic authentication
- Kernel-only creation
- Protected storage

### Fine-Grained Access
- Per-resource capabilities
- Minimal permissions
- Principle of least privilege

### Revocation
- Immediate effect
- Cascading revocation
- Audit trail

### Delegation Control
- Reduced permissions only
- Tracked lineage
- Time-bounded validity

## Performance Optimizations

### Capability Caching
```c
// Per-CPU capability cache
__thread cap_cache_t local_cache[CAP_CACHE_SIZE];
```

### Fast Validation Path
```c
// Bloom filter for quick rejection
if (!bloom_filter_check(cap)) {
    return VALIDATION_FAILED;  // Fast reject
}
```

### Batched Operations
```c
// Validate multiple capabilities at once
cap_validate_batch(caps, count, results);
```

## Attack Mitigation

### Capability Forgery
- Protection: Cryptographic authentication
- Detection: Invalid token check
- Response: Process termination

### Privilege Escalation
- Protection: Monotonic permission reduction
- Detection: Permission violation
- Response: Capability revocation

### Use-After-Revoke
- Protection: Immediate invalidation
- Detection: Stale capability check
- Response: Access denial

## Audit and Logging

### Logged Events
- Capability creation
- Failed validations
- Revocations
- Delegations

### Audit Record
```c
struct audit_record {
    timestamp_t time;
    pid_t process;
    cap_id_t capability;
    audit_event_t event;
    result_t result;
};
```

## Testing Strategy

### Unit Tests
- Capability lifecycle
- Authentication algorithms
- Reference counting

### Security Tests
- Forgery attempts
- Revocation propagation
- Permission enforcement

### Performance Tests
- Validation latency
- Cache hit rates
- Scalability limits

## Future Enhancements

### Quantum-Resistant
- Lattice-based signatures
- Post-quantum cryptography
- Hybrid authentication

### Distributed Capabilities
- Network-wide validity
- Byzantine fault tolerance
- Consensus protocols

### Hardware Integration
- TPM support
- Hardware security modules
- Secure enclaves
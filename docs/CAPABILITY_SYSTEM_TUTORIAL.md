# PDAC Capability System V2 - Tutorial

**A Beginner-Friendly Guide to the ExoV6 Capability-Based Security System**

---

## Table of Contents

1. [Introduction](#introduction)
2. [What Are Capabilities?](#what-are-capabilities)
3. [Getting Started](#getting-started)
4. [Basic Capability Operations](#basic-capability-operations)
5. [Advanced Features](#advanced-features)
6. [Real-World Examples](#real-world-examples)
7. [Best Practices](#best-practices)
8. [Troubleshooting](#troubleshooting)

---

## Introduction

Welcome! This tutorial will teach you how to use the PDAC (Probabilistic DAG Algebra with Capabilities) security system in the ExoV6 kernel. By the end of this guide, you'll understand:

- What capabilities are and why they're powerful
- How to allocate, use, and manage capabilities
- How to implement dynamic security policies with lambda formulas
- How to pass capabilities between processes using zero-copy IPC

**Prerequisites:** Basic C programming knowledge, familiarity with operating system concepts.

**Time to Complete:** ~30 minutes

---

## What Are Capabilities?

### The Problem with Traditional Security

Traditional operating systems (like Unix) use **Access Control Lists (ACLs)** for security. For example:

```
/home/user/secret.txt: owner=user, group=staff, permissions=rw-r-----
```

**Problems:**
- **Ambient Authority:** Programs run with all your permissions (overkill for simple tasks)
- **Confused Deputy:** Programs can be tricked into using your permissions maliciously
- **Hard to Audit:** Can't easily track which programs access which files

### The Capability Solution

A **capability** is an **unforgeable token** that grants specific rights to a specific resource.

```
Capability #42:
  Resource:  File "/home/user/secret.txt"
  Rights:    READ (not WRITE)
  Owner:     Process 100
```

**Benefits:**
- **Least Privilege:** Programs get only what they need
- **No Confused Deputy:** Can't access resources without explicit capability
- **Easy Delegation:** Pass capabilities to other programs safely
- **Fine-Grained:** Separate caps for reading, writing, executing

### Real-World Analogy

**ACLs are like house keys:**
- One key opens all doors
- If stolen, attacker has full access
- Hard to lend to someone temporarily

**Capabilities are like hotel keycards:**
- Each card opens specific doors
- Cards can expire automatically
- Easy to issue temporary cards
- Can revoke cards remotely

---

## Getting Started

### Step 1: Initialize the Capability Table

Before using capabilities, initialize the global capability table:

```c
#include "capability_v2.h"

void kernel_main(void) {
    /* Initialize capability system */
    capv2_table_init();

    printf("Capability system ready!\n");
}
```

The capability table holds 4096 slots (2.5 MB total). Each slot can store one capability.

### Step 2: Allocate Your First Capability

Let's create a capability for a memory page:

```c
#include "capability_v2.h"

void example_allocate_capability(void) {
    /* Define resource quotas (8D vector) */
    resource_vector_t quota = {
        .cpu = Q16(0.5),      /* 50% CPU */
        .memory = Q16(1024),  /* 1 MB */
        /* Other dimensions default to 0 */
    };

    /* Allocate capability */
    int slot = capv2_alloc(
        0x1000,                     /* Resource ID (physical address) */
        CAP_TYPE_MEMORY_PAGE,       /* Type of resource */
        CAP_RIGHT_READ | CAP_RIGHT_WRITE,  /* Rights bitmask */
        quota                       /* Resource quota */
    );

    if (slot < 0) {
        printf("Error: %d\n", slot);
        return;
    }

    printf("Allocated capability at slot %d\n", slot);
}
```

**What just happened?**
- We created a capability for memory page at address `0x1000`
- Granted READ and WRITE rights (but not EXECUTE)
- Limited to 1 MB memory and 50% CPU usage
- Capability stored in slot `slot` (e.g., slot #5)

---

## Basic Capability Operations

### Checking Rights

Before accessing a resource, check if you have the required rights:

```c
void example_check_rights(int cap_slot) {
    /* Check if we have READ right */
    int ret = capv2_check_rights(cap_slot, CAP_RIGHT_READ);
    if (ret == CAPV2_OK) {
        printf("✓ Have READ permission\n");
        /* Safe to read from resource */
    } else {
        printf("✗ Permission denied\n");
        return;
    }

    /* Check for multiple rights */
    ret = capv2_check_rights(cap_slot, CAP_RIGHT_READ | CAP_RIGHT_WRITE);
    if (ret == CAPV2_OK) {
        printf("✓ Have READ and WRITE permissions\n");
    }
}
```

### Granting Capabilities (Delegation)

Share a capability with another process (with reduced rights):

```c
void example_grant_capability(int my_slot, uint32_t other_pid) {
    /* Grant read-only access to another process */
    int other_slot = capv2_grant(
        my_slot,           /* Source capability */
        other_pid,         /* Recipient process ID */
        CAP_RIGHT_READ     /* Attenuated rights (READ only) */
    );

    if (other_slot < 0) {
        printf("Grant failed: %d\n", other_slot);
        return;
    }

    printf("Granted read-only capability to PID %u at slot %d\n",
           other_pid, other_slot);
}
```

**Key Concept: Rights Attenuation**
- You can REDUCE rights when granting (READ|WRITE → READ)
- You CANNOT INCREASE rights (READ → READ|WRITE) ❌
- This prevents privilege escalation attacks!

### Revoking Capabilities

Revoke a capability and all its children:

```c
void example_revoke_capability(int cap_slot) {
    int ret = capv2_revoke(cap_slot);
    if (ret == CAPV2_OK) {
        printf("Capability revoked (including all delegated copies)\n");
    }
}
```

**Revocation Tree:**
```
Parent Capability
├── Child 1 (granted to Process A)
│   └── Grandchild 1.1 (granted by Process A to Process B)
└── Child 2 (granted to Process C)
```

Revoking the parent also revokes Child 1, Grandchild 1.1, and Child 2!

### Deriving Capabilities (Quota Partitioning)

Create a child capability with partitioned resources:

```c
void example_derive_capability(int parent_slot) {
    /* Parent has 1 MB quota, give child 256 KB */
    resource_vector_t child_quota = {
        .memory = Q16(256),  /* 256 KB */
    };

    int child_slot = capv2_derive(
        parent_slot,           /* Parent capability */
        child_quota,           /* Child's quota (subtracted from parent) */
        CAP_RIGHT_READ         /* Child's rights */
    );

    if (child_slot < 0) {
        printf("Derive failed: %d\n", child_slot);
        return;
    }

    printf("Derived child capability with 256 KB quota\n");
    /* Parent now has 768 KB remaining (1024 - 256) */
}
```

---

## Advanced Features

### Lambda Formulas (Dynamic Policies)

Instead of static rights, use **formulas** to compute rights dynamically:

#### Example 1: Time-Limited Access

Grant access for 1 hour, then automatically expire:

```c
void example_time_limited_access(int cap_slot) {
    /* Create time-based formula data */
    time_based_formula_data_t *data = malloc(sizeof(*data));
    data->expiry_time = get_current_time() + (60 * 60 * 1000); /* 1 hour */
    data->base_rights = CAP_RIGHT_READ | CAP_RIGHT_WRITE;
    data->expired_rights = 0; /* No rights after expiry */

    /* Attach formula to capability */
    capv2_set_formula(cap_slot, formula_time_based, data);

    printf("Capability will expire in 1 hour\n");
}
```

#### Example 2: Usage Quotas

Allow 100 accesses, then revoke:

```c
void example_usage_quota(int cap_slot) {
    usage_based_formula_data_t *data = malloc(sizeof(*data));
    data->max_accesses = 100;
    data->base_rights = CAP_RIGHT_READ;
    data->quota_exceeded_rights = 0;

    capv2_set_formula(cap_slot, formula_usage_based, data);

    printf("Capability allows 100 accesses\n");
}
```

#### Example 3: Complex Policy (Time AND User)

Grant access IF (time is valid) AND (user is admin):

```c
void example_complex_policy(int cap_slot) {
    /* Time-based sub-policy */
    time_based_formula_data_t *time_data = malloc(sizeof(*time_data));
    time_data->expiry_time = ...;
    time_data->base_rights = 0xFFFFFFFF; /* All rights */

    /* User-based sub-policy */
    user_based_formula_data_t *user_data = malloc(sizeof(*user_data));
    user_data->user_pids[0] = 1; /* Admin PID */
    user_data->user_rights[0] = CAP_RIGHT_READ | CAP_RIGHT_WRITE;
    user_data->num_policies = 1;
    user_data->default_rights = 0;

    /* Combine with AND */
    combinator_formula_data_t *comb = malloc(sizeof(*comb));
    comb->formula1 = formula_time_based;
    comb->data1 = time_data;
    comb->formula2 = formula_user_based;
    comb->data2 = user_data;
    comb->combinator = FORMULA_COMBINATOR_AND;

    capv2_set_formula(cap_slot, formula_combinator, comb);
}
```

### Rate Limiting (Token Buckets)

Prevent denial-of-service attacks with rate limiting:

```c
void example_rate_limiting(int cap_slot) {
    /* Allow 100 burst accesses, then limit to 10/second sustained */
    capv2_enable_rate_limit(cap_slot, Q16(100), Q16(10));

    /* Access with rate limiting */
    for (int i = 0; i < 150; i++) {
        int ret = capv2_check_rights_ratelimited(
            cap_slot,
            CAP_RIGHT_READ,
            Q16(1)  /* Consume 1 token */
        );

        if (ret == CAPV2_ERR_RATE_LIMITED) {
            printf("Rate limited after %d accesses!\n", i);
            break;
        }
    }
}
```

### Zero-Copy IPC

Pass capabilities between processes efficiently:

```c
void example_ipc_file_server(void) {
    /* Client: Request file */
    cap_ipc_buffer_t *req = cap_ipc_create_file_open(
        "/tmp/test.txt",
        O_RDWR,
        0644
    );
    cap_ipc_send(FILE_SERVER_PID, req);

    /* Server: Allocate file descriptor capability */
    resource_vector_t quota = {0};
    int fd_cap = capv2_alloc(
        file_handle,
        CAP_TYPE_FILE_DESCRIPTOR,
        CAP_RIGHT_READ | CAP_RIGHT_WRITE,
        quota
    );

    /* Server: Send response with capability */
    cap_ipc_buffer_t *resp = cap_ipc_create_file_response(0, fd_cap);
    cap_ipc_send(client_pid, resp);

    /* Client: Extract file capability */
    cap_ipc_buffer_t *received;
    cap_ipc_receive(&received);

    int32_t my_fd_cap;
    cap_ipc_extract_capability(
        received,
        offsetof(cap_ipc_file_response_t, file_cap),
        &my_fd_cap
    );

    /* Client can now use fd_cap to access file */
}
```

---

## Real-World Examples

### Example 1: Secure File Server

```c
void secure_file_server_example(void) {
    /* Server owns file capability */
    resource_vector_t quota = {.memory = Q16(1024)};
    int file_cap = capv2_alloc(
        file_inode,
        CAP_TYPE_FILE_DESCRIPTOR,
        CAP_RIGHT_READ | CAP_RIGHT_WRITE | CAP_RIGHT_GRANT,
        quota
    );

    /* Client requests access */
    if (user_has_permission(client_pid, file_inode)) {
        /* Grant read-only to client */
        int client_cap = capv2_grant(
            file_cap,
            client_pid,
            CAP_RIGHT_READ
        );

        /* Send capability via IPC */
        send_capability_to_client(client_pid, client_cap);
    } else {
        send_error_to_client(client_pid, -EPERM);
    }
}
```

### Example 2: Cloud Resource Allocation

```c
void cloud_tenant_isolation_example(void) {
    /* Tenant gets 10 GB RAM, 4 CPUs */
    resource_vector_t tenant_quota = {
        .memory = Q16(10240),  /* 10 GB */
        .cpu = Q16(4.0),       /* 4 CPUs */
    };

    int tenant_cap = capv2_alloc(
        vm_handle,
        CAP_TYPE_RESOURCE_QUOTA,
        CAP_RIGHT_READ | CAP_RIGHT_DERIVE,
        tenant_quota
    );

    /* Tenant creates 2 sub-containers */
    resource_vector_t container1_quota = {.memory = Q16(5120), .cpu = Q16(2.0)};
    resource_vector_t container2_quota = {.memory = Q16(5120), .cpu = Q16(2.0)};

    int cont1 = capv2_derive(tenant_cap, container1_quota, CAP_RIGHT_READ);
    int cont2 = capv2_derive(tenant_cap, container2_quota, CAP_RIGHT_READ);

    /* Now tenant_cap has 0 remaining quota (partitioned to children) */
}
```

---

## Best Practices

### ✅ DO:
- **Use least privilege:** Grant only needed rights
- **Set quotas:** Always specify resource limits
- **Revoke when done:** Free capabilities no longer needed
- **Check rights:** Always call `capv2_check_rights()` before accessing resources
- **Use formulas:** Implement time-based expiry for temporary access

### ❌ DON'T:
- **Don't grant GRANT right:** Unless delegation is explicitly needed
- **Don't skip validation:** Always validate capability slots
- **Don't leak capabilities:** Store securely, don't pass in plain text
- **Don't forget refcounts:** Free capabilities will fail if refcount > 0

---

## Troubleshooting

### Error: `CAPV2_ERR_TABLE_FULL`
**Cause:** All 4096 capability slots are allocated.
**Solution:** Free unused capabilities, or increase `CAP_TABLE_SIZE`.

### Error: `CAPV2_ERR_NO_PERMISSION`
**Cause:** Trying to grant rights you don't have, or missing GRANT/REVOKE right.
**Solution:** Check capability rights with `capv2_get_info()`.

### Error: `CAPV2_ERR_QUOTA_EXCEEDED`
**Cause:** Trying to derive child with quota > parent's available quota.
**Solution:** Reduce child quota or increase parent quota.

### Error: `CAPV2_ERR_RATE_LIMITED`
**Cause:** Token bucket exhausted.
**Solution:** Wait for tokens to refill, or increase capacity/rate.

### Error: `CAPV2_ERR_GENERATION_MISMATCH`
**Cause:** Capability was freed and reallocated (generation counter changed).
**Solution:** Re-acquire capability reference.

---

## Summary

You've learned:

✅ What capabilities are and why they're better than ACLs
✅ How to allocate, use, and manage capabilities
✅ Rights attenuation and secure delegation
✅ Lambda formulas for dynamic policies
✅ Rate limiting with token buckets
✅ Zero-copy IPC for capability passing

**Next Steps:**
- Read `include/capability_v2.h` for full API reference
- Explore `kernel/test_capability_v2.c` for unit tests
- Study examples in `kernel/cap_formula.c` and `kernel/cap_ipc.c`
- Experiment with combining formulas for complex policies

**Further Reading:**
- Original seL4 whitepaper (capability system design)
- Cap'n Proto documentation (zero-copy serialization)
- "Capability Myths Demolished" by Mark Miller et al.

---

**Happy coding with capabilities! 🔐**

*For questions or issues, see `docs/PDAC_UNIFIED_FRAMEWORK.md` for architecture details.*

# Capability Lifecycle Specification

## 1. Overview

This document defines the lifecycle of capabilities in the Phoenix Exokernel PDAC System V2. It addresses creation, delegation, revocation, persistence, and the handling of stale capabilities.

## 2. Capability States

A capability slot in the global kernel table can be in one of the following states:
1.  **FREE**: Available for allocation.
2.  **ALLOCATED**: Valid and owned by a process.
3.  **REVOKED**: Invalidated, waiting for cleanup or zombie state.

## 3. Lifecycle Operations

### 3.1 Creation (`capv2_alloc`)
*   **Trigger**: A process requests a new resource (e.g., allocating a page, creating an IPC channel).
*   **Mechanism**:
    1.  Kernel allocates a slot from the global free list.
    2.  **Generation Counter**: The slot's generation counter is incremented. This is critical for preventing ABA problems (stale handles referring to new objects).
    3.  **Refcount**: Initialized to 1.
    4.  **Quota**: Resource vector is initialized.

### 3.2 Delegation (`capv2_grant` / `capv2_derive`)
*   **Grant**: Moves or shares a capability. If shared, a new slot is often allocated to represent the distinct handle for the recipient.
*   **Derive**: Creates a child capability with a subset of resources/rights.
    *   **Invariant**: `Child.rights <= Parent.rights`.
    *   **Tracking**: The kernel maintains a directed acyclic graph (DAG) or tree of derivation. Parent points to children.

### 3.3 Revocation (`capv2_revoke`)
*   **Recursive Revocation**: Revoking a capability recursively revokes all its children in the derivation tree.
*   **Mechanism**:
    1.  Traverse the descendant tree.
    2.  Mark each slot as invalid/revoked.
    3.  Decrement reference counts on underlying kernel objects.
    4.  If a slot's refcount drops to zero, it is freed.

### 3.4 Stale Capabilities & Safety
*   **Definition**: A "stale" capability is a user-space handle (index) that points to a slot which has been revoked and potentially re-allocated to a different object.
*   **Detection**:
    *   User-space handles are typically tuples: `{index, generation}`.
    *   On every syscall using a capability, the kernel checks:
        ```c
        if (slot[index].generation != handle.generation) {
            return E_STALE_CAP; // Fail cleanly
        }
        ```
*   **Semantics**: Stale capabilities fail cleanly and immediately. They do not grant access to the new object occupying the slot.

## 4. Persistence Strategy

### 4.1 Current State: Runtime-Only
Currently, capabilities are **volatile runtime objects**. They exist only in the kernel's memory (`kernel/capability_v2.c`).

*   **VFS Integration**: The Virtual File System (VFS) and MINIX FS implementation currently use standard POSIX-like access control (inodes/modes) to *bootstrap* capabilities.
    *   When a file is opened, the kernel checks disk permissions (ACLs/Modes).
    *   If authorized, a new runtime capability is minted and returned to the process (wrapped in a file descriptor or direct cap handle).

### 4.2 Persistence on Disk (Future Design)
To persist capabilities directly (e.g., for storing a "power" to a file on disk), the following model is intended:
*   **Extended Attributes**: Capabilities will be serialized into extended attributes (xattrs) of files.
*   **Cryptographic Wrapping**: The capability metadata (rights, quotas) would be signed/encrypted using the kernel's root key or the owner's key (using Kyber for future-proofing) to prevent tampering on disk.
*   **Rehydration**: Upon loading, the kernel verifies the signature and "rehydrates" the capability into a volatile slot.

## 5. Cryptographic Integration (Kyber)

### 5.1 Usage
*   **Key Exchange**: Kyber is used for establishing secure channels between isolated components (lattice nodes).
*   **Side-Channels**:
    *   **Key Rotation**: Keys are currently generated at node initialization. Rotation requires re-establishing the channel (creating new nodes).
    *   **Constant-Time**: The current implementation (`kernel/ipc/lattice_kernel.c`) uses a simplified Kyber model. While loop bounds are fixed, strict constant-time execution for all arithmetic ops is a work in progress.
    *   **Output Sizes**: Output sizes are fixed (static arrays) to prevent length-based side channels in the ABI.

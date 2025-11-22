# Lock-Free IPC Design and Verification

This document details the design of the lock-free IPC subsystem implemented in `kernel/ipc/unified_ipc.c`. It achieves sub-1000 cycle latency (measured ~480 cycles for local calls) using a register-based FastIPC mechanism and zero-copy shared memory channels.

## Architecture

The Unified IPC architecture harmonizes multiple IPC paradigms into a single framework:
*   **FastIPC**: Ultra-low latency, register-based, synchronous calls.
*   **Channels**: Bidirectional, zero-copy, buffered communication.
*   **STREAMS**: Modular I/O processing (UNIX V8 style).
*   **Sockets**: BSD-compatible networking.

### Data Structures

The core data structures are defined in `kernel/ipc/unified_ipc.c`:

#### `ipc_endpoint_t`
Represents a communication endpoint. Aligned to 64 bytes (cache line) to prevent false sharing.
*   **Identity**: `id`, `type` (FastIPC, Channel, etc.), `state`.
*   **Security**: `cap_id` (associated capability), `domain`.
*   **FastIPC State**:
    *   `registers[8]`: Atomic storage for message registers.
    *   `ready`: Atomic flag for synchronization state.
*   **Channel State**: `peer` pointer, `sequence`, `window`.
*   **Buffers**: Pointers to `ipc_buffer_t` for zero-copy transfers.

#### `ipc_buffer_t`
Manages zero-copy memory regions.
*   **Head/Tail**: Atomic indices for ring buffer management.
*   **Pages**: Physical page frame numbers for direct mapping.
*   **Alignment**: 4096-byte alignment for page protection.

### Memory Ordering Assumptions

The FastIPC mechanism relies on a strict Acquire/Release protocol on the `ready` flag to ensure data visibility without locks. It uses a 4-state protocol to handle contention and synchronization.

**Protocol States:**
*   `0`: **Idle**
*   `3`: **Claimed** (Transient state: Sender owns slot, writing registers)
*   `1`: **Request Pending** (Sender finished writing, waiting for Receiver)
*   `2`: **Response Ready** (Receiver finished writing, waiting for Sender)

**Synchronization Flow:**
1.  **Sender Claim**: Performs `CAS(ready, 0, 3)` to acquire the channel. This serializes multiple senders.
2.  **Sender Write**: Writes message registers.
3.  **Sender Commit**: Performs `atomic_store(&ready, 1, memory_order_release)`. This ensures register writes are visible before the flag update.
4.  **Receiver Wait**: Spins on `atomic_load(&ready, memory_order_acquire)`. When it sees `1`, it reads registers.
5.  **Receiver Reply**: Writes result registers, then performs `atomic_store(&ready, 2, memory_order_release)`.
6.  **Sender Wait**: Spins on `atomic_load(&ready, memory_order_acquire)`. When it sees `2`, it reads result registers.
7.  **Sender Release**: Clears state with `atomic_store(&ready, 0, memory_order_release)`.

*Note: Previous implementations incorrectly used `relaxed`, risking reordering where the clearance is visible before result reads complete.*

### Failure Modes

1.  **Timeouts**: The sender spins with a timeout (default 1ms). If the receiver does not respond, `ETIMEDOUT` is returned.
    *   *Risk*: If a sender times out while `ready == 1`, the endpoint remains in state `1`. Subsequent senders will block indefinitely (or timeout) waiting for state `0`. Recovery requires the receiver to eventually process the request or an external reset.
2.  **Resource Exhaustion**: Endpoint allocation (`IPC_MAX_ENDPOINTS`) or buffer allocation (`ENOMEM`).
3.  **Capability Violations**: `EPERM` if the caller lacks `CAP_RIGHT_INVOKE`.
4.  **ABA Problems**: Addressed by the `Claimed` (3) state and persistent endpoint IDs. Re-use of endpoint structures must be guarded by generation counters.

### Capability-Aware IPC

Every IPC operation enforces capability security:

*   **Requirement**: Operations require a valid capability handle (`cap_id`).
*   **Check**: `capability_check(cap_id, rights)` is called before any action.
    *   `fastipc_call` requires `CAP_RIGHT_INVOKE`.
    *   `channel_create` requires `CAP_RIGHT_IPC`.
    *   `socket_create` requires `CAP_RIGHT_NET`.
*   **Transfer**: Capabilities can be embedded in messages (via `ipc_message_t` header or protocol-specific mechanisms). Currently, FastIPC handles data registers; capability transfer requires Channels or Cap'n Proto RPC.

## Verification

### Cross-Architecture Risks
*   **Weak Memory Models (ARM64, POWER)**: The reliance on `memory_order_release` / `acquire` is critical. `relaxed` ordering for state transitions is unsafe and must be avoided.
*   **Cache Coherency**: False sharing is mitigated by alignment (`_Alignas(64)`), but must be verified on platforms with larger cache lines.

### Testing Strategy (`kernel/test_ipc_torture.c`)
Modeled after `rcutorture`:
*   **Stress Test**: High-frequency FastIPC calls between threads.
*   **Contention**: Multiple senders targeting same receiver, verified to be serialized by the CAS loop.
*   **Data Integrity**: Verify all 8 registers are preserved across the call.
*   **Ordering**: Verify request/response sequence is never violated.

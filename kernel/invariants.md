# Exokernel Core Invariants

This document enumerates the core invariants (I) and safety properties (S) of the ExoV6 kernel.
These invariants are partially mapped to formal specifications in `formal/specs/`.

## 1. Capabilities
*Ref: `formal/specs/Capability.tla`*

*   **I1**: No kernel API exposes raw kernel pointers to userland. All access is via opaque `cap_t` handles.
*   **I2**: Each valid `cap_t` is unique per resource instance and generation.
*   **I3**: Any use of `cap_t` must check rights bits (e.g., `CAP_RIGHT_SEND`) before performing operations.
*   **I4**: A capability must be valid (exist in the global capability table) to be used.
*   **I5**: Capability revocation is atomic; once revoked, the handle is invalid immediately.

## 2. Channels & IPC
*Ref: `formal/specs/StreamsLocks.tla`*

*   **I6**: Channels must satisfy no lost messages and no duplication (reliable delivery).
*   **I7**: FIFO ordering is guaranteed for messages from a single sender to a single receiver.
*   **I8**: Lock acquisition order must be consistent (e.g., `spinlock` -> `qspinlock`) to prevent deadlocks.
*   **I9**: Memory safety for ring buffers is enforced via atomic indices and boundary checks.

## 3. Scheduling (Beatty)
*Ref: `kernel/sched_beatty.c`*

*   **I10**: Task selection occurs in O(1) time.
*   **I11**: Long-run CPU share approximates target weights within bounded deviation (Beatty's Theorem).
*   **I12**: Ready queue operations are atomic with respect to interrupt handlers.

## 4. Architecture & Concurrency

*   **I13**: RCU critical sections must not block, sleep, or yield the CPU.
*   **I14**: All lock-free structures must use explicit C11 `memory_order` primitives (e.g., `memory_order_acquire/release`).
*   **I15**: Per-CPU data structures are only accessed by the owning CPU unless explicitly protected by locks.

## 5. Security (Lattice)

*   **I16**: Information flow must respect lattice dominance:
    *   Read permitted iff `Label(Subject) >= Label(Object)`.
    *   Write permitted iff `Label(Subject) <= Label(Object)`.
*   **I17**: Capabilities carry a `label_t` that is immutable after creation.

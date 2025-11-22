# Exokernel Core Invariants

This document outlines the core invariants and architectural principles of the Phoenix Exokernel.

## 1. Unified Kernel Architecture

*   **Single Source Tree**: All core kernel code resides in the `kernel/` directory.
*   **Monolithic Compilation**: The kernel is compiled as a single binary (`kernel`), facilitating whole-program optimization.
*   **No Dynamic Modules**: To ensure stability and security, the kernel does not load dynamic modules at runtime. All drivers and subsystems are statically linked or run in userspace.

## 2. Capability-Based Resource Management

The kernel adheres to a strict Exokernel philosophy where the kernel's role is to securely multiplex physical resources, not to abstract them.

*   **Everything is a Capability**: Access to all resources (memory pages, interrupts, I/O ports, DMA channels, block devices) is mediated by capabilities (`exo_cap`).
*   **All capabilities are 128‑bit opaque values; no other forms of resource IDs exist.**
*   **Explicit Binding**: Userspace must explicitly bind resources. For example:
    *   `exo_bind_irq`: Bind an interrupt to a process.
    *   `exo_bind_block`: Bind a block device range for direct I/O.
*   **No Implicit Allocation**: The kernel rarely allocates memory implicitly. Userspace provides buffers for operations (e.g., `exo_bind_block` takes a user-provided `struct buf`).

## 3. Concurrency & Synchronization

The kernel employs a unified concurrency model designed for low latency and scalability on multicore systems.

*   **Spinlocks**: Used for short critical sections. Implemented with `PAUSE` instructions to be hyperthread-friendly.
    *   **Invariant**: Spinlocks must be held for short durations. Interrupts are often disabled (`pushcli`/`popcli`) while holding a spinlock to prevent deadlocks.
*   **Sleeplocks**: Used for long-running operations where the thread may need to yield.
    *   **Invariant**: A thread holding a sleeplock may be preempted or sleep.
*   **Atomic Operations**: Extensive use of C11-style atomic primitives (`atomic_cas`, `atomic_add`) and memory barriers (`smp_mb`) for lock-free structures.
*   **All lock‑free structures must only use atomics with explicit memory orders; memory_order_seq_cst is banned except in specific files.**
*   **RCU (Read-Copy-Update)**: Supported for read-mostly data structures to ensure scalability.
    *   **Allowed Usage**: RCU is permitted for read-mostly data structures (e.g. scheduler, VFS).
    *   **Prohibited Contexts**: RCU primitives (`rcu_read_lock`, `rcu_synchronize`) must NOT be used during early boot (before `rcuinit`) or in single-CPU initialization phases.
    *   **Runtime Assertions**: Debug builds must enforce these invariants by panicking on invalid usage.

## 4. Execution Model

*   **Explicit Scheduling**: The kernel supports multiple pluggable schedulers (Beatty, DAG, Lottery).
*   **Direct Control Flow**: System calls like `sys_ipc_fast` perform direct context switches or buffer copies to reduce overhead.
*   **No Hidden Control Flow**: The kernel does not perform complex background tasks hidden from the user. Services like the `reaper` or `swapper` are explicit kernel threads or userspace services.
*   **All user pointers must be validated before dereference.**

## 5. Address Space & Isolation

*   **Page Tables**: Hardware page tables (x86_64 `CR3`) enforce isolation.
*   **Kernel Map**: The kernel is mapped into the higher half of every address space.
*   **User/Kernel Separation**: Strict separation of privileges (CPL 0 vs CPL 3).
*   **Capability Guards**: Even with a valid virtual address, operations on resources (like checking an IRQ) require a valid capability token.

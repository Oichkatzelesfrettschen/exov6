# Observability Discipline

## Overview
Observability is critical for understanding system behavior, diagnosing issues, and optimizing performance in the Phoenix Exokernel.

## Components

### 1. Kernel Logs
*   **Ring Buffer**: The kernel maintains a circular log buffer for high-speed logging.
*   **Levels**: `DEBUG`, `INFO`, `WARN`, `ERROR`, `PANIC`.
*   **Access**: Exposed via a system call or a virtual device (`/dev/klog` in LibOS).

### 2. Tracing
*   **Static Tracepoints**: Key kernel events (syscall entry/exit, scheduler tick, IRQ) have static tracepoints.
*   **Dynamic Tracing**: (Planned) Support for eBPF-like dynamic probes.
*   **Output**: Traces can be emitted to the serial console or a memory buffer for post-processing.

### 3. Performance Counters
*   **Hardware**: PMU integration for CPU cycles, cache misses, etc.
*   **Software**: Kernel counters for:
    *   Syscalls per second
    *   Context switches
    *   Capability lookups (hits/misses)
    *   Memory allocation stats

### 4. Debug Interface (`debugfs`)
A virtual filesystem interface for inspecting kernel state at runtime.
*   **Mount**: `mount -t debugfs none /sys/kernel/debug`
*   **Nodes**:
    *   `/sched`: Scheduler state (runqueues, Beatty sequence stats).
    *   `/mem`: Memory allocator stats.
    *   `/caps`: Active capabilities (restricted access).

## Best Practices
*   **Structured Logging**: Use structured formats (key=value) where possible for machine parsing.
*   **Sampling**: Use sampling for high-frequency events to avoid overhead.
*   **Privacy**: Do not log sensitive data (user keys, content).

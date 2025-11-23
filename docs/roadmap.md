# Phoenix Exokernel Roadmap & Implementation Guide

This document outlines the stepwise engineering and implementation plan for achieving advanced features in the Phoenix Exokernel and LibOS.

## 3.A Full Linux Binary Compatibility Layer
- [ ] **Analyze Syscall Requirements**: Identify critical syscalls for target workloads (Coreutils, Nginx, Redis).
- [ ] **Define APIs**: Create `include/linux_compat.h` mapping `SYS_*` constants.
- [ ] **Stub Implementation**: Create `libos/posix/linux_abi.c` with a central dispatcher.
- [ ] **Incremental Implementation**: Implement `write`, `read`, `open`, `close`, `mmap`, `brk`.

## 3.B BSD Socket Implementation Completion
- [ ] **Map BSD Calls**: Direct socket syscalls to internal LibOS networking stack.
- [ ] **Implement Core Functions**: `socket`, `bind`, `listen`, `accept`, `connect`, `send`, `recv`.
- [ ] **Backend Integration**: Use Shared Memory Ring Buffers (Unified IPC) for local transport.

## 3.C Container and Virtualization Support
- [ ] **Namespaces**: Implement `CLONE_NEWPID`, `CLONE_NEWNET`, `CLONE_NEWNS`.
- [ ] **Isolation**: Virtualize Process IDs and mount points.
- [ ] **Cgroups**: Integrate resource accounting into the Scheduler and Memory Allocator.

## 3.D GPU Computing Offload Framework
- [ ] **API Design**: Define `vgpu_submit` and command buffer formats in `include/gpu/vgpu.h`.
- [ ] **Memory Management**: Implement GART-like aperture management using `exo_bind_block`.
- [ ] **Driver Wrapper**: Create `libos/gpu/vgpu.c` to interface with the mock kernel driver.

## 3.E Real-Time Extensions for Industrial Use
- [ ] **Scheduler Update**: Add `SCHED_FIFO` and `SCHED_RR` classes to `sched_beatty.c`.
- [ ] **Preemption**: Implement cooperative preemption points in kernel hotspots.
- [ ] **Priority Inheritance**: Add PI logic to Mutex primitives.

## 3.F DPDK Integration for Networking
- [ ] **DPDK Setup**: Link against `librte_eal` and `librte_ethdev`.
- [ ] **Hugepages**: Manage hugepage mappings via `exo_alloc_page`.
- [ ] **Fast Path**: Expose a zero-copy packet API (`libos_packet_rx`/`tx`).

## 3.G Multi-Architecture Support
- [ ] **Toolchain Setup**: Configure CMake for `riscv64` and `aarch64`.
- [ ] **CI Matrix**: Define build variants in `CMakeLists.txt`.

## 3.H Performance Tuning
- [ ] **Profiling**: Use `perf` and `valgrind` (on host) to analyze LibOS behavior.
- [ ] **Optimization**: Reduce syscall dispatch overhead and memcpy operations.

## 3.I Advanced Security Features
- [ ] **CET**: Enable Intel Control-flow Enforcement Technology (`-fcf-protection`).
- [ ] **PAC**: Enable ARM Pointer Authentication (`-mbranch-protection`).
- [ ] **Hardening**: Enable Stack Canaries and ASLR.

## 3.J Formal Verification
- [ ] **Modeling**: Model the Capability security properties in TLA+.
- [ ] **Verification**: Run model checkers to prove isolation invariants.

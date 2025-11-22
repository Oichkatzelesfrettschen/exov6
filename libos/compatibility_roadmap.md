# LibOS Compatibility Roadmap: Linux, BSD, Containers, GPU, and RT

This document outlines the granular roadmap for achieving comprehensive compatibility with Linux binaries, BSD sockets, containerization, GPU offload, and Real-Time extensions within the Phoenix Exokernel LibOS.

## 1. Linux Binary Compatibility Layer

**Goal**: Enable unmodified Linux ELF binaries to run on Phoenix LibOS.

**Strategy**:
*   **Syscall Translation**: Implement a userspace syscall dispatcher that intercepts x86_64 `syscall` instructions (via kernel upcall or binary rewriting) and maps Linux syscall numbers (RAX) to LibOS internal functions.
*   **VDSO**: Provide a Virtual Dynamic Shared Object (VDSO) to accelerate `gettimeofday`, `clock_gettime`, and `getcpu`.
*   **Procfs/Sysfs**: Emulate `/proc` and `/sys` file systems using a synthetic in-memory file system.

**Granular Tasks**:
1.  [ ] Define Linux syscall numbers in `include/linux_compat.h`.
2.  [ ] Implement `linux_syscall_dispatch` in `libos/posix/linux_abi.c`.
3.  [ ] Implement `brk` and `mmap` with Linux flags compatibility.
4.  [ ] Implement `arch_prctl` (FS/GS base setting) support.
5.  [ ] Validate with statically linked "Hello World" Linux binary.

## 2. BSD Socket Implementation Completion

**Goal**: Full BSD Sockets API (socket, bind, connect, accept, listen, send, recv, poll/select).

**Strategy**:
*   **Unified IPC Backend**: Map socket operations to the kernel's "Unified IPC" (FastIPC/Shared Memory).
*   **Userspace TCP/IP**: Integrate a lightweight userspace TCP/IP stack (e.g., lwIP or a custom Rust-based stack) running as a "Network Service" process.
*   **Zero-Copy**: Use buffer passing capability for high-performance I/O.

**Granular Tasks**:
1.  [ ] Create `libos/net/socket.c` to replace host wrappers.
2.  [ ] Define `struct socket` and `struct sock` file descriptors.
3.  [ ] Implement `AF_UNIX` using `exo_ipc` channels.
4.  [ ] Implement `AF_INET` hooking into a virtual network interface.
5.  [ ] Implement `epoll` simulation for event notification.

## 3. Container and Virtualization Support

**Goal**: Native support for Namespaces (PID, NET, MNT, IPC, UTS, USER) and Cgroups.

**Strategy**:
*   **Namespaces**: Add `struct nsproxy` to the process Control Block (PCB) in LibOS.
*   **Isolation**: Modify ID generation (getpid) and resource lookups (sockets, mounts) to be namespace-aware.
*   **Cgroups**: Implement resource accounting (CPU time, Memory usage) in `sched_beatty.c` and memory allocators.

**Granular Tasks**:
1.  [ ] Add `struct namespace` to `struct process` in `libos/process.h`.
2.  [ ] Implement `unshare()` and `setns()` syscalls.
3.  [ ] Virtualize `getpid()` to return namespace-relative PIDs.
4.  [ ] Implement `chroot` and `pivot_root` equivalents.

## 4. GPU Computing Offload Framework

**Goal**: A standardized API for submitting compute kernels to accelerators (Simulated or Passthrough).

**Strategy**:
*   **Command Queues**: Implement a ring-buffer based command submission interface (`ioctl` style).
*   **Memory Sharing**: Use `exo_bind_page` to share buffers between CPU and GPU contexts.
*   **Virtual GPU**: Create a software-simulated GPU device for testing.

**Granular Tasks**:
1.  [ ] Define `vgpu_cmd_t` structure in `include/gpu/vgpu.h`.
2.  [ ] Implement `/dev/vgpu0` device driver in LibOS.
3.  [ ] Create a library `libvgpu` for userspace context creation and command submission.
4.  [ ] Implement a basic Compute Shader IR processor (mock).

## 5. Real-time Extensions

**Goal**: Deterministic scheduling and low-latency response (PREEMPT_RT like).

**Strategy**:
*   **Scheduler Classes**: Augment `sched_beatty` to support `SCHED_FIFO` and `SCHED_RR` with strict priority.
*   **Preemption**: Add explicit preemption points in long-running kernel/LibOS paths.
*   **Priority Inheritance**: Implement PI mutexes to avoid priority inversion.

**Granular Tasks**:
1.  [ ] Add `uint32_t priority` and `uint32_t policy` to `dag_task_t`.
2.  [ ] Modify `beatty_pick_next` to check RT queues first.
3.  [ ] Implement `sched_setscheduler` and `sched_getparam`.
4.  [ ] Add high-resolution timers for wakeups.

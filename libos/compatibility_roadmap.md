# LibOS Compatibility Roadmap: POSIX, BSD, and SVR4

This document outlines the long-term roadmap for achieving comprehensive compatibility with POSIX, BSD, and SVR4 operating system personalities within the FeuerBird LibOS.

## 1. Introduction

FeuerBird's exokernel design delegates most operating system functionalities to user-space Library Operating Systems (LibOSes). This roadmap details the phased approach to building a robust and feature-complete LibOS that can host applications designed for traditional Unix-like environments.

## 2. Scope and Challenges

Achieving full compatibility involves implementing a vast array of system calls, library functions, and environmental behaviors. Key challenges include:

- **System Call Emulation:** Translating POSIX/BSD/SVR4 system calls into sequences of exokernel primitives (capabilities, IPC, direct hardware access).
- **Resource Management:** Implementing user-space file systems, process management (fork/exec), memory management (mmap, sbrk), and inter-process communication (pipes, sockets) on top of exokernel capabilities.
- **Signal Handling:** Replicating complex signal semantics in user space, including signal delivery, masking, and handlers.
- **Device Abstraction:** Providing generic device interfaces (e.g., character devices, block devices, network interfaces) that map to exokernel-exposed hardware resources.
- **Concurrency and Synchronization:** Implementing user-space threading models and synchronization primitives.
- **Locale and Internationalization:** Providing comprehensive locale support.
- **Performance:** Ensuring that the user-space implementations do not introduce unacceptable overhead compared to monolithic kernel approaches.

## 3. High-Level Plan

### Phase 1: Core POSIX (Current Focus)

- **File System:** Implement a robust user-space file system (e.g., UFS-like) using exokernel disk block capabilities.
- **Process Management:** Basic fork/exec, process lifecycle management, and PID mapping.
- **Basic IPC:** Pipes and simple message queues built on exokernel IPC primitives.
- **Memory Management:** Basic mmap/munmap and sbrk using page capabilities.

### Phase 2: Advanced POSIX and BSD

- **Advanced File System Features:** Permissions, extended attributes, journaling.
- **Networking:** Full socket API implementation, including TCP/IP stack in user space.
- **Signals:** Comprehensive signal handling, including signal sets, handlers, and inter-process signaling.
- **Threading:** POSIX threads (pthreads) implementation.
- **BSD Specifics:** Implementing BSD-specific system calls and library functions.

### Phase 3: SVR4 and Full Feature Parity

- **SVR4 Specifics:** Implementing SVR4-specific system calls and behaviors.
- **Advanced Device Drivers:** Implementing more complex user-space drivers for various hardware (e.g., advanced network cards, specialized peripherals).
- **Performance Tuning:** Extensive profiling and optimization of all LibOS components to achieve near-native performance.
- **Certification:** Pursuing formal POSIX/BSD/SVR4 certification if applicable.

## 4. Directory Structure for LibOS Components

To maintain modularity and clarity, the `libos/` directory will be organized as follows:

- `libos/posix/`: POSIX-specific syscall wrappers and library functions.
- `libos/bsd/`: BSD-specific syscall wrappers and library functions.
- `libos/svr4/`: SVR4-specific syscall wrappers and library functions.
- `libos/fs/`: User-space file system implementation.
- `libos/net/`: User-space networking stack.
- `libos/proc/`: User-space process and thread management.
- `libos/drivers/`: User-space device driver implementations.
- `libos/crypto/`: Cryptographic libraries (e.g., for Lattice IPC).
- `libos/util/`: Common utility functions.

This structured approach will facilitate parallel development and clear separation of concerns.

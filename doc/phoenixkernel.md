# Phoenix Kernel Overview

The Phoenix kernel implements an exokernel research platform built on top of the xv6 code base. Its goal is to expose low-level hardware resources directly to user space while keeping the in-kernel portion as small as possible. Applications link against a library operating system (libOS) that provides traditional services on top of the primitive capability interface.

## Exokernel Philosophy

Phoenix follows the exokernel approach: the kernel multiplexes hardware resources and enforces protection but leaves higher-level abstractions to user-level code. Instead of implementing full POSIX semantics in the kernel, Phoenix exposes capabilities that grant controlled access to memory regions, devices and communication endpoints. User-space runtimes build whatever abstractions they require.

## DAG Execution Model

Scheduling is expressed as a directed acyclic graph (DAG) of tasks. Nodes represent units of work and edges encode explicit dependencies. The kernel traverses this graph whenever a context switch is required, allowing cooperative libraries to chain execution without relying on heavyweight kernel threads. The DAG model enables fine-grained scheduling, efficient data-flow processing and transparent composition of user-level schedulers.

## Capability System

All privileged operations require an explicit capability token. Capabilities are unforgeable references that encode the rights a holder has over a particular object. They are used to control access to physical memory, I/O ports, endpoints and other resources. Messages may carry badges identifying the sender so that libraries can implement higher-level security policies entirely in user space.

## Directory Layout

A suggested layout for projects building on Phoenix is:

- `src-kernel/`   – core kernel source files
- `src-uland/`    – user-space programs and the basic C library
- `libos/`        – the Phoenix libOS implementing POSIX-style services
- `include/`      – shared headers for both kernel and user space
- `doc/`          – design notes and other documentation

Keeping kernel, user programs and the libOS separated helps manage dependencies and clarifies which components operate at which privilege level.

## Building

The repository uses GNU Make. To build the kernel image run:

```
make kernel
```

This compiles everything under `src-kernel/` and links the `exo-kernel` binary. The default `make` target also assembles a bootable `xv6.img` disk image containing this kernel.

To build the user-space library operating system invoke:

```
make libos
```

which produces `libos.a`. Applications link against this archive to access the capability wrappers, filesystem code and user-level scheduler located in `libos/` and `src-uland/`.

## POSIX Compatibility in User Space

Phoenix itself does not provide a POSIX interface. Instead the libOS layers POSIX system calls on top of the capability primitives. Files, processes and IPC endpoints are implemented in user space, allowing multiple runtimes to coexist. Programs written against POSIX headers simply link against `libos.a` and run unmodified on the exokernel.


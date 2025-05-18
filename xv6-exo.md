# xv6 Exokernel Extensions

This document summarizes the experimental exokernel version of xv6.  It
introduces the capability primitives, outlines the new system calls, and
explains the role of the library operating system (LibOS) used with the
exokernel.  For a background on the ideas behind exokernels see the
canonical papers *Exokernel: An Operating System Architecture for
Application-Level Resource Management* (Engler et al., 1995) and *ExOS: An
Application-Level Operating System* (Engler et al., 1997).  The original
MIT prototype was called **Aegis**.

## Capability primitives

The exokernel variant exposes hardware resources using capabilities.  A
capability is an opaque handle granting access to a resource such as a
physical memory page, CPU time slice, or device.  User programs may pass
capabilities between each other to share resources.

Capabilities are issued by the kernel and checked on each access.  Unlike
standard xv6, the kernel does not implement high-level abstractions such
as files or processes.  Instead, user-space code builds these abstractions
by combining capabilities.

## New system calls

Several system calls are added to manage capabilities and low-level
resources:

* `capalloc` – request a capability for a resource (e.g., a page frame).
* `capfree`  – release a previously acquired capability.
* `capgrant` – grant a capability to another protection domain.
* `caprevoke` – revoke a capability that was previously granted.
* `exosched` – yield the CPU or set a scheduling parameter.

These calls form the basis on which a LibOS can build higher-level
primitives such as processes, virtual memory, and file descriptors.

## LibOS responsibilities

Because the kernel only multiplexes resources, user-level libraries
provide traditional operating-system services.  The LibOS linked with
applications implements process creation, the file system interface,
and higher-level memory management.  Different LibOS implementations can
coexist, allowing specialized applications to trade convenience for
performance or control.

## Building and running

Building the standard xv6 kernel is unchanged:

```
make qemu
```

To build the exokernel version pass `EXO=1` when invoking `make`.  This
produces `kernel-exo` and accompanying disk images:

```
make EXO=1 qemu
```
The non-EXO and EXO builds use separate output files so you can keep both around for comparison. Consult the Makefile for additional targets.

## Further reading

For more details on exokernel design see:

* Dawson R. Engler, M. Frans Kaashoek, and James O'Toole.
  *Exokernel: An Operating System Architecture for Application-Level Resource Management.*
  Proceedings of the Fifteenth ACM Symposium on Operating Systems Principles, 1995.
* Dawson R. Engler, M. Frans Kaashoek, and others.
  *ExOS: An Application-Level Operating System.*  Technical report, MIT, 1997.


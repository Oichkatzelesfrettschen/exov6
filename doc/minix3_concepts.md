# MINIX 3 Concepts Influencing Phoenix Exokernel

MINIX 3 demonstrates how user-space drivers and small system services can run
outside the kernel. A minimal kernel handles context switches and message-based
IPC. When a driver fails, the **Reincarnation Server** restarts it without a
system reboot. Services communicate using short messages passed through the
kernel.

Phoenix adapts these ideas within an exokernel that exposes hardware resources
through a libOS and userland. We plan to port MINIX-style capabilities for
user-space drivers, process supervision and message-based IPC while keeping
other Phoenix internals private. Endpoints and typed channels already offer a
capability interface, making the MINIX approach a natural fit.

Cap'n Proto RPC will serialize messages sent over these endpoints. Its schema
language aligns with the typed channel design and supports a **multi calculus**
model inspired by λ-calculus.

## High-Level Implementation Plan

1. Extend the libOS to launch drivers and services as regular user programs
   communicating via endpoint capabilities.
2. Add a lightweight supervisor patterned after the Reincarnation Server to
   detect failures and restart drivers automatically.
3. Switch IPC calls to Cap'n Proto messages exchanged over typed channels.
4. Limit public documentation to the MINIX-inspired features while keeping other
   Phoenix details internal.

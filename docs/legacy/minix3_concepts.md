# MINIX 3 Concepts Influencing FeuerBird Exokernel

MINIX 3 demonstrates how user-space drivers and small system services can run
outside the kernel. A minimal kernel handles context switches and message-based
IPC. When a driver fails, the **Reincarnation Server** restarts it without a
system reboot. Services communicate using short messages passed through the
kernel.

FeuerBird adapts these ideas within an exokernel that exposes hardware resources
through a libOS and userland. We plan to port MINIX-style capabilities for
user-space drivers, process supervision and message-based IPC while keeping
other FeuerBird internals private. Endpoints and typed channels already offer a
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
   FeuerBird details internal.

## rcrs Driver Supervisor

FeuerBird's supervisor, `rcrs`, mirrors the MINIX Reincarnation Server.  It reads
`drivers.conf` at boot to know which drivers to launch.  Each non-empty line in
the file is a command line for a user-space driver.  The supervisor pings all
running drivers through an endpoint.  If a process exits or fails to respond
before its timeout expires, `rcrs` kills and restarts it.  A restart counter and
the current process ID are shown in periodic status reports so clients can
reconnect when a driver is replaced.

Example workflow:

1. `drivers.conf` contains `kbdserv` and `pingdriver --timeout=60`.
2. `rcrs` starts both drivers and begins pinging them.
3. A crash or `kill -9` terminates `kbdserv`.
4. `rcrs` logs `kbdserv exited, restarting (count=1)` and launches a new
   instance with a new PID.
5. Clients listening to the status output reconnect to the restarted service.

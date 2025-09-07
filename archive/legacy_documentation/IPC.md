# Interprocess Communication Overview

This note summarizes the evolving IPC design for xv6.

### Fast-path call
A specialized entry allows a user process to invoke a service through a direct
function call. The goal is to bypass the usual trap sequence and reduce the
cost of short, synchronous requests.

### Capability badges
Capabilities carry small integer badges that identify the holder and constrain
which endpoints or channels they may access. The badge travels with the message
so receivers can authenticate the sender without additional lookup.

### Proposed features
* **Endpoints** act as rendezvous points for message passing. They are intended
  to provide fine-grained control similar to L4's endpoints and Mach ports.
* **Typed channels** attach metadata describing the expected message format so
  senders and receivers can verify compatibility at compile time.

### Influences
The design borrows from several sources:
* Microkernel IPC mechanisms from L4 and Mach inspired the endpoint interface.
* Theoretical work in the λ-calculus informs the functional style of the
  fast-path call, while π-calculus motivates the notion of typed channels.


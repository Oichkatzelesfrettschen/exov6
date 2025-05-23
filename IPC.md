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

### Typed channel API
Typed channels pair a `chan_t` descriptor with a `msg_type_desc` describing the
expected message layout.  The helper functions `chan_endpoint_send()` and
`chan_endpoint_recv()` validate the buffer length against this descriptor before
forwarding to the underlying capability IPC primitives.  A typical usage is:

```c
CHAN_DECLARE(ping_chan, DriverPing);

ping_chan_t *c = ping_chan_create();
DriverPing m = { .value = 7 };
exo_cap cap = {0};
ping_chan_send(c, cap, &m);
ping_chan_recv(c, cap, &m);
ping_chan_destroy(c);
```

### Influences
The design borrows from several sources:
* Microkernel IPC mechanisms from L4 and Mach inspired the endpoint interface.
* Theoretical work in the λ-calculus informs the functional style of the
  fast-path call, while π-calculus motivates the notion of typed channels.


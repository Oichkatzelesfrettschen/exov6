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

## Capability Primitives

The kernel surface is intentionally small.  Applications manipulate raw
hardware resources via capability objects and a handful of system calls.
Each call takes or returns an `exo_cap` structure defined in
`include/exokernel.h`.

### Memory Pages

- `exo_alloc_page()` – allocate a physical page and obtain a capability
  describing it.  The page is not automatically mapped.
- `exo_unbind_page(cap)` – free the page referenced by `cap` and remove
  any mappings to it.

```c
// Allocate a page and later release it
exo_cap page = exo_alloc_page();
/* map_page is provided by the libOS */
void *va = map_page(page.id);
use_memory(va);
exo_unbind_page(page);
```

### Disk Blocks

- `exo_alloc_block(dev, rights)` – obtain a capability for a free disk
  block on device `dev` with the requested access rights.
- `exo_bind_block(&cap, buf, write)` – perform a block read or write
  using `buf` as the transfer buffer.  `write` selects the direction.
- `exo_flush_block(&cap, data)` – helper that writes `data` to the block
  referenced by `cap`.

### Direct I/O

- `exo_read_disk(cap, dst, off, n)` – read arbitrary byte ranges from a
  block capability.
- `exo_write_disk(cap, src, off, n)` – write bytes at the given offset.

### Context Switching

- `exo_yield_to(target)` – switch execution to the context referenced by
  `target`.  Cooperative schedulers store contexts in user space and
  resume them with this call.

The scheduler iterates over tasks through the **exo_stream** callbacks
`exo_stream_yield()` and `exo_stream_halt()`.  Schedulers such as the DAG
engine register their `struct exo_sched_ops` with
`exo_stream_register()` so the kernel can invoke the appropriate logic
whenever the current task yields or no runnable work remains.

### IPC

- `exo_send(dest, buf, len)` – enqueue a message to the destination
  capability.
- `exo_recv(src, buf, len)` – receive data from the source capability.
- `zipc_call(msg)` – perform a fast IPC syscall using the `zipc_msg_t`
  structure defined in `ipc.h`.

Typed channels built with the `CHAN_DECLARE` macro wrap these primitives
and automatically serialize Cap'n Proto messages.

The libOS builds higher level abstractions such as processes and files
by combining these primitives.

## Running the Demos

Several user programs demonstrate the capability API.  After building
the repository the filesystem image contains `exo_stream_demo`,
`dag_demo`, `typed_chan_demo` and `chan_dag_supervisor_demo`.

1. Build everything:

   ```
   make
   ```

2. Start the system under QEMU:

   ```
   make qemu-nox
   ```

3. At the xv6 shell run one of the demos:

   ```
   $ exo_stream_demo
   $ dag_demo
   $ typed_chan_demo
   $ chan_dag_supervisor_demo
   ```

Both programs print messages from their stub implementations showing how
`exo_yield_to` and the DAG scheduler hooks would be invoked.


## Driver Processes

Hardware devices are managed entirely from user space. A driver runs as a
regular Phoenix process holding capabilities that provide access to the
corresponding I/O regions and interrupts. A crashed or misbehaving driver
cannot compromise the kernel because it only receives the capabilities it
needs. Drivers typically export a Cap'n Proto service describing the
operations they support.

## Supervisor

The supervisor is a small user-space monitor started at boot. It launches
all driver processes and restarts them if they exit unexpectedly. The
supervisor passes the initial capability set to each driver and watches for
death notifications so that dependent clients can reconnect to the newly
started instance.

## Cap'n Proto IPC

Phoenix uses [Cap'n Proto](https://capnproto.org/) schemas to describe the
messages exchanged between processes. The fast endpoint-based IPC mechanism
transports serialized Cap'n Proto messages. Applications define their RPC
interfaces in `.capnp` files and rely on the Cap'n Proto C bindings to
generate the encoding and decoding routines.

### Typed Channels

For convenience the libOS provides typed channels declared with the
`CHAN_DECLARE` macro in `chan.h`.  Each typed channel associates a Cap'n
Proto message type with a channel descriptor so that `send` and `recv`
automatically encode and decode the messages.  The Cap'n Proto workflow
generates `<name>.capnp.h` files defining `type_MESSAGE_SIZE` constants
and the corresponding `type_encode`/`type_decode` helpers.  A typed channel
uses these helpers to serialize exactly `msg_size` bytes when interacting
with an endpoint.  See `typed_chan_demo.c` for an example.

## libOS APIs

The libOS includes wrappers around the capability syscalls as well as helper
routines for writing user-level services. Important entry points are
provided in `caplib.h` and `libos/libfs.h`:

```c
exo_cap cap_alloc_page(void);
int cap_unbind_page(exo_cap cap);
int cap_send(exo_cap dest, const void *buf, uint64 len);
int cap_recv(exo_cap src, void *buf, uint64 len);
int fs_alloc_block(uint dev, uint rights, struct exo_blockcap *cap);
int fs_read_block(struct exo_blockcap cap, void *dst);
int fs_write_block(struct exo_blockcap cap, const void *src);
```

These helpers make it straightforward to allocate memory pages, exchange
messages and perform basic filesystem operations from user space.

## Writing a Simple Driver

A minimal block driver illustrating these APIs is shown below:

```c
#include "caplib.h"
#include "libos/libfs.h"
#include "user.h"

int main(void) {
    struct exo_blockcap blk;
    fs_alloc_block(1, EXO_RIGHT_R | EXO_RIGHT_W, &blk);
    char buf[BSIZE] = "Phoenix";
    fs_write_block(blk, buf);
    memset(buf, 0, sizeof(buf));
    fs_read_block(blk, buf);
    printf(1, "driver read: %s\n", buf);
    return 0;
}
```

Compile the file with `make` and add the resulting binary to the disk image.
The supervisor can then spawn the driver at boot time or restart it if it
exits.

### Driver Management Helpers

Convenience functions in `libos/driver.h` assist with launching and
connecting to drivers:

```c
int driver_spawn(const char *path, char *const argv[]);
int driver_connect(int pid, exo_cap ep);
```

`driver_spawn` forks and executes the given program while
`driver_connect` sends an endpoint capability to an already running
driver.

## Step-by-Step Examples

The following walkthroughs illustrate how common Phoenix primitives fit
together.  Each snippet can be compiled as a standalone program and run
inside the xv6 environment.

### Capability Allocation

1. Allocate a physical page and map it in user space.
2. Use the memory and then release the capability.

```c
#include "caplib.h"
#include "user.h"

int
main(void)
{
    exo_cap page = exo_alloc_page();
    void *va = map_page(page.id); // provided by the libOS
    memset(va, 0, PGSIZE);
    exo_unbind_page(page);
    return 0;
}
```

### Typed Channel Example

1. Declare a typed channel using `CHAN_DECLARE`.
2. Send a Cap'n Proto message and wait for the reply.

```c
#include "chan.h"
#include "proto/ping.capnp.h"

CHAN_DECLARE(ping_chan, ping_MESSAGE_SIZE);

int
main(void)
{
    struct ping msg = ping_init();
    ping_chan_send(&ping_chan, &msg);
    ping_chan_recv(&ping_chan, &msg);
    return 0;
}
```

### Driver Management Example

1. Spawn a driver process with `driver_spawn`.
2. Connect to its endpoint and exchange a test message.

```c
#include "libos/driver.h"

int
main(void)
{
    int pid = driver_spawn("blk_driver", 0);
    exo_cap ep = obtain_driver_ep(pid); // helper returning the endpoint
    driver_connect(pid, ep);
    return 0;
}
```

## Beatty Scheduler and Affine Runtime

Work is underway on a Beatty scheduler that enables affine scheduling of
tasks.  Once the implementation lands this section will describe its API
and how the affine runtime integrates with existing DAG scheduling.

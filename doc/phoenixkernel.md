#Phoenix Kernel Overview

The Phoenix kernel implements an exokernel research platform built on top of the
        xv6 code base.Its goal is to expose low -
    level hardware resources directly to user space while keeping the in -
    kernel portion as small as possible.Applications
        link against a library operating
        system(libOS)
that provides traditional services on top of the primitive capability interface.

    ##Exokernel Philosophy

        Phoenix follows the exokernel approach
    : the kernel multiplexes hardware resources and
          enforces protection but leaves higher -
    level abstractions to user -
    level code.Instead of implementing full POSIX semantics in the kernel,
    Phoenix exposes capabilities that grant controlled access to memory regions,
    devices and communication endpoints.User -
        space runtimes build whatever abstractions they require.

        ##DAG Execution Model

            Scheduling is expressed as a directed acyclic
            graph(DAG) of tasks. Nodes represent units of work and edges encode explicit dependencies. The kernel traverses this graph whenever a context switch is required, allowing cooperative libraries to chain execution without relying on heavyweight kernel threads. The DAG model enables fine-grained scheduling, efficient data-flow processing and transparent composition of user-level schedulers.

A second **Beatty scheduler** now complements the DAG engine. It alternates between an arbitrary number of contexts using Beatty sequences with irrational weights. Call `beatty_sched_set_tasks` with an array of task capabilities and the corresponding weights to activate it. The scheduler is registered as an exo stream so user-level runtimes can select it on demand.

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

## BSD and SVR4 Compatibility Goals

While the current focus is POSIX emulation, the project also aims to
support BSD and System&nbsp;V Release&nbsp;4 personalities entirely in user
space.  Additional modules under `libos/` will translate Phoenix
capabilities to the expected interfaces.  Planned components include
`bsd_signals.c` and `bsd_termios.c` for the classic BSD signal and
terminal APIs, and `svr4_signal.c` along with `svr4_termios.c` to mimic
their SVR4 counterparts.  Linking these libraries will let applications
run with a BSD or SVR4 flavour without altering the kernel.

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
and automatically serialize Cap'n Proto messages.  Each channel is
backed by a `msg_type_desc` describing the size of the Cap'n Proto
structure it transports.

Schemas written in `.capnp` format are compiled with `capnp` to generate
`<name>.capnp.h`.  The resulting header defines `type_MESSAGE_SIZE` as
well as `type_encode()` and `type_decode()` helpers that translate
between the C struct and its serialized form.

The generic helpers `chan_endpoint_send()` and `chan_endpoint_recv()`
verify that the buffer length matches the descriptor before invoking the
underlying capability syscalls.  A mismatch causes the helpers to return
`-1` (and the kernel variant prints a diagnostic), ensuring that only
properly sized messages traverse the channel.

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

The `rcrs` supervisor runs at boot and keeps drivers alive. It launches each program listed in `drivers.conf` and pings them periodically through an endpoint. If a driver fails to respond before the timeout expires `rcrs` kills and restarts it. Status reports show the process IDs and restart counts so clients can reconnect when a driver is replaced.

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

The underlying helpers `chan_endpoint_send()` and `chan_endpoint_recv()`
verify that the buffer length matches the `msg_type_desc` before calling
`exo_send` or `exo_recv`.  Both kernel and user space use the same
validation logic so mismatched messages are rejected early.

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

### User-Space Filesystem

The legacy kernel file system has been moved entirely into the libOS.  Module
`libos/fs_ufs.c` manages a tiny in-memory directory of files, each backed by a
block capability obtained with `exo_alloc_block`.  Calls such as
`libfs_open()` and `libfs_read()` operate on these capabilities with
`exo_bind_block` so the kernel only sees raw disk accesses.  POSIX wrappers in
`libos/posix.c` now use this API instead of invoking system calls.

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


### Affine Runtime

The libOS offers an **affine runtime** for experimenting with linear
resource tracking.  An affine channel may be used at most once for
sending and once for receiving.  The helper functions declared in
`libos/affine_runtime.h` mirror the generic channel API but enforce the
single-use property:

```c
affine_chan_t *affine_chan_create(const struct msg_type_desc *desc);
void affine_chan_destroy(affine_chan_t *c);
int affine_chan_send(affine_chan_t *c, exo_cap dest,
                     const void *msg, size_t len);
int affine_chan_recv(affine_chan_t *c, exo_cap src,
                     void *msg, size_t len);
```

Lambda terms are represented by `lambda_term_t` and executed with
`lambda_run()` which deducts a unit of fuel for every evaluation step:

```c
typedef int (*lambda_fn)(void *env);

typedef struct lambda_term {
  lambda_fn fn; // one step evaluator
  void *env;    // closure environment
  int steps;    // total steps executed
} lambda_term_t;

int lambda_run(lambda_term_t *t, int fuel);
```

This lightweight accounting mechanism allows research into affine
λ-calculus interpreters while integrating with Phoenix's typed channel
infrastructure.

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

The kernel now ships with a Beatty scheduler implementing an affine runtime. It dispatches multiple cooperating contexts according to irrational weights. Enable it with `beatty_sched_set_tasks` after registering the Beatty exo stream. Typed channels can exchange messages whenever the scheduler yields.

When `beatty_dag_stream_init()` is invoked during boot the Beatty scheduler is chained with the DAG scheduler through a single exo stream. Beatty picks the next task family based on its irrational weights and then defers to the DAG scheduler to run the individual ready nodes. This allows user space runtimes to build dependency graphs while still benefiting from the affine time slicing provided by Beatty. Selecting the combined stream merely requires calling the initializer before submitting DAG nodes.


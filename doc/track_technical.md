# Technical Track

This guide outlines the low level Phoenix interfaces and how programs interact with the libOS. It should be read together with the [Phoenix kernel charter](phoenixkernel.md).

## Kernel API Summary

Phoenix provides a minimal capability interface. Important calls include:

- `exo_alloc_page()` and `exo_unbind_page()` for physical pages.
- `exo_alloc_block()` and `exo_bind_block()` for disk blocks.
- `endpoint_send()` and `endpoint_recv()` for message passing.
- DAG scheduling primitives for user controlled execution.

Each call manipulates an `exo_cap` structure that represents the rights to a resource.

## Using the libOS

The libOS implements POSIX style abstractions in user space. Applications link against `libos.a` to gain helpers such as file descriptors, process management and memory mapping. Typical usage is:

```c
exo_cap page = exo_alloc_page();
void *va = map_page(page.id); /* provided by libOS */
/* ... use memory via POSIX wrappers ... */
exo_unbind_page(page);
```

More detailed examples live in the charter and the source tree under `engine/libos/` and `engine/user/`.
# Phoenix Technical Track

This track provides a high level summary of the public APIs exported by Phoenix.
The charter outlines the full scope and goals of the project.

## Capability Primitives

- `exo_alloc_page()` / `exo_unbind_page()` – allocate and free physical pages.
- `exo_alloc_block()` / `exo_bind_block()` – manage disk blocks.
- `exo_yield_to()` – switch to a user controlled context.
- `exo_send()` / `exo_recv()` – fast message passing between endpoints.

The IPC helpers return an `exo_ipc_status` value declared in
`engine/include/exo_ipc.h`:

- `IPC_STATUS_SUCCESS` – message delivered or received.
- `IPC_STATUS_TIMEOUT` – wait timed out.
- `IPC_STATUS_AGAIN`   – destination mailbox was full.
- `IPC_STATUS_BADDEST` – invalid endpoint capability.

These calls are thin wrappers around the kernel interface.  Higher layers
are implemented in the libOS.

## libOS APIs

The user mode library builds on the capabilities to expose POSIX like
services. Key entry points include:

```c
exo_cap cap_alloc_page(void);
int cap_unbind_page(exo_cap cap);
int cap_send(exo_cap dest, const void *buf, uint64 len);
int cap_recv(exo_cap src, void *buf, uint64 len);
```

Typed channels declared with `CHAN_DECLARE` automatically serialise Cap'n
Proto messages for these helpers.

See the project charter for a complete list of supported calls.

## Lambda Capabilities

The affine runtime includes a small framework for **lambda capabilities**.
These objects pair a capability token with a lambda term.  A lambda
capability may be *consumed* exactly once via `lambda_cap_use()`.  After the
lambda executes the underlying capability is considered spent and further
calls fail.

```c
lambda_cap_t *lambda_cap_create(lambda_fn fn, void *env, exo_cap cap);
int lambda_cap_use(lambda_cap_t *cap, int fuel);
int lambda_cap_delegate(lambda_cap_t *cap, uint16_t new_owner);
int lambda_cap_revoke(lambda_cap_t *cap);
```

Delegation increments the reference count so another task can hold the token.
Revocation uses the kernel to invalidate the capability by bumping its epoch.
Microkernels can replace these hooks to perform additional checks before a
capability is transferred or revoked.

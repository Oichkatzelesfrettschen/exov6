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

More detailed examples live in the charter and the source tree under `libos/` and `src-uland/`.
# Phoenix Technical Track

This track provides a high level summary of the public APIs exported by Phoenix.
The charter outlines the full scope and goals of the project.

## Capability Primitives

- `exo_alloc_page()` / `exo_unbind_page()` – allocate and free physical pages.
- `exo_alloc_block()` / `exo_bind_block()` – manage disk blocks.
- `exo_yield_to()` – switch to a user controlled context.
- `exo_send()` / `exo_recv()` – fast message passing between endpoints.

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

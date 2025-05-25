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

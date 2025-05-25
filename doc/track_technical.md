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

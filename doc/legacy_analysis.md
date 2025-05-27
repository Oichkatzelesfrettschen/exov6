# Legacy Component Analysis

This document tracks how the original xv6 sources map to the evolving
Phoenix architecture.  Each entry lists the component's role today,
what will replace it, and the current migration status.  Update this
file whenever code is removed or rewritten to keep a clear view of the
remaining legacy pieces.

| Component | Current Role | Phoenix Replacement | Status |
|-----------|--------------|---------------------|--------|
| `proc.c` | Process table and old in-kernel scheduler. | Capability-based process containers. User space schedulers drive execution via `exo_stream` and DAG hooks. | Kernel scheduler removed; capability IDs replace global PIDs. |
| `runqueue.c` | Simple FIFO list of runnable processes. | User schedulers maintain their own queues. Kernel only switches to the chosen context. | Only used by compatibility stubs. |
| `vm.c` | Sets up page tables and manages virtual memory. | Capability spaces with page caps allocated through `exo_alloc_page()`. | Fully converted to capability spaces. |
| `syscall.c`, `sysproc.c` | POSIX style system call table. | Minimal capability interface (`exo_alloc_page`, `exo_yield_to`, `exo_send`, ...). POSIX lives in libOS. | Many old syscalls removed; more to drop. |
| `fs.c`, `file.c`, `sysfile.c` | In-kernel filesystem and descriptor management. | User-space file servers using block and directory capabilities. | Logic moved to `filesrv` managed by `rcrs`. |
| `trap.c` | Interrupt vectors and fault handling. | Minimal handlers for capability traps and message passing. Fault upcalls handled in user space. | Mostly unchanged except for timer gas accounting. |
| `exo_ipc.c`, `endpoint.c` | Kernel queues for IPC. | Typed channels built on capability endpoints. | Basic endpoints implemented; queues moving out of kernel. |
| Drivers (`ide.c`, `tty.c`, ...) | Built-in device drivers. | User-space drivers managed by the `rcrs` supervisor. | Kernel drivers removed. |

## Eliminated Features
- Fixed scheduler policy inside the kernel.
- Several legacy syscalls (`chdir`, `sleep`, etc.) now implemented purely in user space.
- Buffer cache simplified for capability-based storage.
- All memory allocation tracked through capability spaces.
- Filesystem and drivers migrated to user-mode services.

## Work Still Needed
* Continue shrinking compatibility shims until no kernel blocking paths remain.

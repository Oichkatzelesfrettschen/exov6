# LibOS / Kernel ABI Definition

This document defines the explicit ABI between the Phoenix Exokernel and the Library OS (LibOS).

## 1. System Call Interface

The kernel exposes functionality via the `syscall` instruction on x86_64.

### Calling Convention (System V AMD64)

*   **Instruction**: `syscall`
*   **System Call Number**: `RAX`
*   **Arguments**: `RDI`, `RSI`, `RDX`, `R10`, `R8`, `R9`
*   **Return Value**: `RAX`
    *   Non-negative: Success
    *   Negative: Error code (e.g., `-EINVAL`)
*   **Clobbered Registers**: `RCX`, `R11` (as per x86_64 `syscall` instruction)

## 2. System Calls

The system call numbers are defined in `include/syscall.h`.

| Number | Name | Description |
| :--- | :--- | :--- |
| 1 | `SYS_fork` | Create a copy of the current process (Legacy/Monolithic) |
| 2 | `SYS_exit` | Terminate the current process |
| 3 | `SYS_wait` | Wait for a child process to change state |
| 4 | `SYS_pipe` | Create an inter-process channel |
| 5 | `SYS_kill` | Send a signal to a process |
| 6 | `SYS_exec` | Execute a new program |
| 7 | `SYS_getpid` | Get current process ID |
| 8 | `SYS_sbrk` | Change data segment size |
| 9 | `SYS_sleep` | Sleep for a specified duration |
| 10 | `SYS_uptime` | Get system uptime |
| 11 | `SYS_mappte` | Map a page table entry |
| 13 | `SYS_exo_alloc_page` | Allocate a physical page (Exokernel) |
| 14 | `SYS_exo_unbind_page` | Release a physical page capability (Exokernel) |
| 15 | `SYS_exo_alloc_block` | Allocate a disk block capability |
| 16 | `SYS_exo_bind_block` | Bind a block capability to a buffer |
| 17 | `SYS_exo_flush_block` | Flush a block to disk |
| 18 | `SYS_exo_yield_to` | Yield CPU to a specific capability |
| 19 | `SYS_exo_read_disk` | Read from disk using capability |
| 20 | `SYS_exo_write_disk` | Write to disk using capability |
| 21 | `SYS_exo_send` | Send IPC message |
| 22 | `SYS_exo_recv` | Receive IPC message |
| 33 | `SYS_cap_inc` | Increment capability refcount |
| 34 | `SYS_cap_dec` | Decrement capability refcount |
| 36 | `SYS_exo_irq_alloc` | Allocate IRQ capability |
| 44 | `SYS_service_register` | Register a system service |

*Note: Calls 1-10 are legacy monolithic calls that should eventually be implemented in LibOS using Exokernel primitives (11+).*

## 3. Shared Data Structures

### 3.1. Capabilities (`exo_cap`)

Defined in `include/exo.h`.

```c
typedef struct exo_cap {
    uint32_t pa;         /* Physical address or Type discriminator */
    uint32_t id;         /* Resource identifier (e.g., IRQ number) */
    uint32_t rights;     /* Bitmask of granted rights */
    uint32_t owner;      /* PID of the owner */
    hash256_t auth_tag;  /* Cryptographic proof of validity */
} exo_cap;
```

**Rights:**
*   `EXO_CAP_READ` (0x1)
*   `EXO_CAP_WRITE` (0x2)
*   `EXO_CAP_EXECUTE` (0x4)

### 3.2. Block Capabilities (`exo_blockcap`)

```c
typedef struct exo_blockcap {
    uint32_t dev;        /* Device ID */
    uint32_t blockno;    /* Block number */
    uint32_t rights;     /* Access rights */
    uint32_t owner;      /* Owner PID */
} exo_blockcap;
```

## 4. Invariants and Rules

1.  **Opaque Kernel Pointers**: LibOS must NEVER dereference a kernel pointer. All kernel objects are accessed via Handles (Capabilities).
2.  **Fail-Fast**: Invalid capabilities result in immediate failure or process termination.
3.  **Capability ownership**: A capability is valid only if `auth_tag` matches the kernel's secret key (HMAC) and `owner` matches the calling process (or is delegated).
4.  **Stateless Kernel**: Ideally, the kernel keeps minimal state. LibOS manages process tables, file tables, etc. (The current implementation of `fork` violates this and is transitional).

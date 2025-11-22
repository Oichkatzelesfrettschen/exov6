# LibOS / Kernel ABI

This document defines the Application Binary Interface (ABI) between the Phoenix Exokernel and the Library OS (LibOS).

## 1. System Call Interface

The kernel exposes functionality via a system call interface invoked using the `syscall` instruction on x86_64.

### Calling Convention

*   **Instruction**: `syscall`
*   **System Call Number**: Passed in `RAX`.
*   **Arguments**: Passed in `RDI`, `RSI`, `RDX`, `R10`, `R8`, `R9` (System V AMD64 ABI style).
*   **Return Value**: Returned in `RAX`.
    *   Non-negative values indicate success.
    *   Negative values indicate error codes (e.g., `-1`, `-EINVAL`).

### System Call Numbers

The system call numbers are defined in `include/syscall.h`. Key ranges include:

*   **POSIX Compatibility**: `1` - `10` (fork, exit, wait, pipe, etc.)
*   **Memory Management**: `11` - `14` (mappte, exo_alloc_page, exo_unbind_page)
*   **Block Device**: `15` - `20` (exo_alloc_block, exo_bind_block, read/write)
*   **IPC**: `21` - `25`, `35` (exo_send, exo_recv, fast_ipc)
*   **Capabilities**: `33` - `34`, `36` - `43` (cap_inc, cap_dec, irq/dma alloc)
*   **Service**: `44` - `45` (service_register)

## 2. Data Structures

The ABI relies on several key data structures shared between kernel and userspace.

### 2.1. Capabilities (`exo_cap`)

The fundamental unit of authority. defined in `include/exo.h`.

```c
typedef struct exo_cap {
    uint32_t pa;         /* Physical address or Type discriminator */
    uint32_t id;         /* Resource identifier (e.g., IRQ number) */
    uint32_t rights;     /* Bitmask of granted rights */
    uint32_t owner;      /* PID of the owner */
    hash256_t auth_tag;  /* Cryptographic proof of validity */
} exo_cap;
```

**Rights Constants:**
*   `EXO_CAP_READ` (0x1)
*   `EXO_CAP_WRITE` (0x2)
*   `EXO_CAP_EXECUTE` (0x4)

### 2.2. Block Capabilities (`exo_blockcap`)

Specific capability for block device access.

```c
typedef struct exo_blockcap {
    uint32_t dev;        /* Device ID */
    uint32_t blockno;    /* Block number */
    uint32_t rights;     /* Access rights */
    uint32_t owner;      /* Owner PID */
} exo_blockcap;
```

## 3. Error Handling

*   **Fail-Fast**: The kernel checks capabilities immediately. Invalid capabilities result in immediate failure (often `-1` or a specific negative error code).
*   **Panic**: In cases of critical kernel state corruption detected during a syscall, the kernel may panic (halt), though this is avoided for user errors.

## 4. IPC Protocol

*   **Fast IPC (`sys_ipc_fast`)**:
    *   Directly copies data from source address space to target address space.
    *   Requires `exo_cap` for the target process.
    *   Zero-copy mechanisms available for larger transfers via shared memory pages.

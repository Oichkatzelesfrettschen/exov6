# How to Write a New LibOS Module

This guide explains how to add a new module to the FeuerBird LibOS.

## Module Structure

A LibOS module typically consists of:

1.  **Public API**: Defined in `include/libos/<module>.h`.
2.  **Implementation**: Located in `libos/<module>.c` or `libos/subsystem/`.
3.  **Capability Translation**: Code to translate high-level operations into exokernel capability invocations.

## Step-by-Step Guide

### 1. Design the Interface

Decide whether the module implements a standard POSIX interface or a custom API.

*   **POSIX**: Implement standard functions (e.g., `open`, `read`, `ioctl`) and integrate with the VFS or device layer.
*   **Custom**: Define a new header file in `include/libos/`.

### 2. Implement the Logic

The implementation should reside in `libos/`.

```c
// libos/mysubsystem.c
#include <libos/mysubsystem.h>
#include <syscall.h>

int libos_my_op(int handle, void *data) {
    // 1. Resolve handle to capability
    cap_t cap = libos_get_cap(handle);
    if (!cap) return -1;

    // 2. Perform IPC with Kernel or Service
    return syscall_invoke(cap, data);
}
```

### 3. Capability Integration

Ensure your module respects the capability system. Do not bypass checks. Use `kernel/cap.c` primitives if running in kernel mode (for hybrid modules) or `syscall` if running in user mode.

### 4. Build System Registration

Add your source files to `libos/CMakeLists.txt` and `libos/meson.build`.

```cmake
# libos/CMakeLists.txt
list(APPEND LIBOS_SOURCES mysubsystem.c)
```

### 5. Testing

Add a test case in `tests/libos/` to verify functionality.

## Best Practices

*   **Zero-Copy**: Use shared memory buffers for large data transfers.
*   **Async I/O**: Integrate with `io_uring` or the async queue system if the operation is blocking.
*   **Thread Safety**: Ensure global state is protected if the module is shared across threads.

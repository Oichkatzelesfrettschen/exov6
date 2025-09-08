# The Phoenix Exokernel - Unified Kernel

This is THE ONE kernel implementation for the Phoenix Exokernel project.
All kernel code has been unified, synthesized, and harmonized into this single directory.

## Structure

```
kernel/
├── boot/           # Boot code and initialization
├── drivers/        # Device drivers
├── fs/             # Filesystem implementation
├── include/        # Kernel-internal headers
├── ipc/            # Inter-process communication
├── mem/            # Memory management
├── sched/          # Process scheduling
├── sync/           # Synchronization primitives
├── sys/            # System calls
├── tests/          # Kernel test modules
└── time/           # Time and clock management
```

## Key Components

- **arbitrate.c**: Resource arbitration and allocation
- **crypto.c**: Cryptographic functions for capabilities
- **spinlock.h**: Unified spinlock implementation
- **sleeplock.h**: Sleep locks for blocking synchronization
- **buf.h**: Buffer cache management

## Building

The kernel is built as part of the main CMake build system:

```bash
mkdir build && cd build
cmake .. -DCMAKE_BUILD_TYPE=Release
make kernel
```

## Testing

Test modules are available in the `tests/` subdirectory and can be
enabled with `-DBUILD_TESTS=ON` during CMake configuration.

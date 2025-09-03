# FeuerBird Exokernel

A POSIX-2024 (SUSv5) compliant exokernel operating system written in C17 that separates mechanism from policy. Originally based on Unix v6, enhanced with modern exokernel capabilities.

## Quick Start

```bash
# Configure and build
mkdir build && cd build
cmake .. -DCMAKE_BUILD_TYPE=Release
cmake --build . -j$(nproc)

# Run in QEMU
cmake --build . --target qemu

# Run tests
ctest -V
```

## Features

### Core Exokernel
- **Minimal kernel**: Raw hardware multiplexing with protected control transfer
- **Capability-based security**: 65536 slots with HMAC-SHA256 authentication
- **Fast IPC**: Zero-copy message passing
- **Pluggable schedulers**: DAG and Beatty schedulers
- **Native x86_64**: No cross-compilation needed

### POSIX Compliance
- **POSIX-2024 (SUSv5)**: Full errno (133 codes), signals (31+), pthreads
- **Core utilities**: cat, ls, cp, mv, pwd, test, grep, wc, and more
- **LibOS layer**: User-space POSIX implementation over exokernel
- **C17 standard**: Modern C with safety features

### Three-Zone Architecture
1. **Kernel Zone** (Ring 0): Hardware multiplexing and capability enforcement
2. **LibOS Zone** (Ring 3, Privileged): POSIX services and system libraries
3. **Application Zone** (Ring 3, User): Unix applications

## Building

### Requirements
- CMake 3.20+
- Native C17 compiler (GCC 8+ or Clang 10+)
- QEMU for testing
- Python 3.8+ with pytest

### Build Options

```bash
# Debug build with features
cmake .. -DCMAKE_BUILD_TYPE=Debug \
         -DUSE_TICKET_LOCK=ON \
         -DIPC_DEBUG=ON \
         -DCONFIG_SMP=ON

# Release build
cmake .. -DCMAKE_BUILD_TYPE=Release
```

### CMake Options
- `USE_TICKET_LOCK`: Enable ticket-based spinlocks
- `USE_CAPNP`: Cap'n Proto IPC support
- `USE_SIMD`: SIMD optimizations
- `IPC_DEBUG`: IPC debugging output
- `CONFIG_SMP`: Multi-core support

## Development

### Testing
```bash
# All tests
ctest -V

# POSIX compliance
cmake --build . --target posix-test

# Code quality
cmake --build . --target lint
cmake --build . --target format
```

### Debugging
```bash
# Terminal 1: Start QEMU with GDB
cmake --build . --target qemu-gdb

# Terminal 2: Connect GDB
gdb kernel.elf
(gdb) target remote :26000
(gdb) break main
(gdb) continue
```

## Project Structure

```
exov6/
├── kernel/          # Core exokernel (78 C files)
│   ├── cap*.c      # Capability system
│   ├── exo*.c      # Exokernel primitives
│   └── fastipc.c   # Fast IPC
├── libos/           # POSIX layer (30 C files)
│   ├── posix.c     # POSIX interfaces
│   ├── pthread*.c  # Threading
│   └── signal*.c   # Signals
├── user/            # Utilities (227 C files)
│   ├── sh.c        # Shell
│   └── *.c         # POSIX utilities
├── include/         # Headers
├── tests/           # Test suite
├── CMakeLists.txt  # CMake configuration
└── kernel.ld       # Linker script
```

## Implementation Status

### Completed ✅
- Core exokernel with capabilities
- Basic POSIX layer (errno, signals, pthreads)
- Essential utilities (cat, ls, cp, mv, etc.)
- Fast IPC implementation
- Multi-core support

### Known Issues 🔧
- Code duplication: Many utility variants (`*_real.c`, `*_simple.c`)
- Multiple spinlock implementations need consolidation
- Limited test coverage

### Roadmap 📋
- Complete POSIX-2024 compliance (150+ utilities)
- Network stack implementation
- Advanced filesystems
- GPU compute support

## Performance

Target metrics:
- IPC latency: < 1000 cycles
- Context switch: < 2000 cycles
- Capability validation: < 100 cycles
- Boot time: < 1 second

## Contributing

See [CONTRIBUTING.md](CONTRIBUTING.md) for guidelines.

## Documentation

- [CLAUDE.md](CLAUDE.md) - Development guide
- [ARCHITECTURE.md](ARCHITECTURE.md) - System design
- [docs/](docs/) - Additional documentation

## License

MIT License (original xv6) with exokernel enhancements.

## References

- POSIX.1-2024 (SUSv5) Specification
- Exokernel papers (MIT)
- xv6 original (MIT)
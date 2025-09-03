# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

FeuerBird is a POSIX-2024 (SUSv5) compliant exokernel operating system written in C17. It implements separation of mechanism from policy through a three-zone architecture (Kernel, LibOS, Application) with capability-based security. Originally based on Unix v6, it uses modern C17 standards and CMake for native builds.

**IMPORTANT**: This is a C17 project using CMake for native x86_64 builds. No cross-compilation needed.

## Build Commands (CMake + Native Compiler)

### Initial Setup
```bash
# Create build directory
mkdir build && cd build

# Configure with CMake
cmake .. -DCMAKE_BUILD_TYPE=Release

# Or with options
cmake .. -DCMAKE_BUILD_TYPE=Debug \
         -DUSE_TICKET_LOCK=ON \
         -DIPC_DEBUG=ON
```

### Building
```bash
# Build everything
cmake --build . -j$(nproc)

# Build specific target
cmake --build . --target kernel.elf
cmake --build . --target fs.img

# Clean build
cmake --build . --target clean
```

### Running
```bash
# Run in QEMU
cmake --build . --target qemu

# Run without graphics
cmake --build . --target qemu-nox

# Debug with GDB
cmake --build . --target qemu-gdb
# In another terminal: gdb kernel.elf -ex "target remote :26000"
```

### Testing
```bash
# Run all tests
ctest -V

# Run Python tests
cmake --build . --target pytest_suite

# POSIX compliance tests
cmake --build . --target posix-test

# Specific test
./build/test_capabilities
```

### Code Quality
```bash
# Format code
cmake --build . --target format

# Run linter
cmake --build . --target lint

# Static analysis
cmake --build . --target analyze
```

## Architecture

### Three-Zone Model
```
Application Zone (Ring 3, User)
    ↕ Capabilities (65536 slots)
LibOS Zone (Ring 3, Privileged)  
    ↕ Secure Bindings
Kernel Zone (Ring 0, Native)
```

### Directory Structure

**Kernel** (`kernel/` - organized by subsystem):
```
kernel/
├── boot/        # Boot and initialization (bootmain.c, main.c, main64.c)
├── drivers/     # Device drivers (console, kbd, uart, mp, lapic, ioapic)
├── fs/          # File system (fs.c, bio.c, ide.c, log.c)
├── ipc/         # IPC and capabilities (cap.c, exo_ipc.c, fastipc.c)
├── mem/         # Memory management (vm.c, kalloc.c, mmu64.c)
├── sched/       # Scheduling (proc.c, beatty_sched.c, dag_sched.c)
├── sync/        # Synchronization (spinlock.c, sleeplock.c, rcu.c, modern_locks.c)
├── sys/         # System calls (syscall.c, trap.c, exec.c)
└── hypervisor/  # Hypervisor support
```

**Locking Implementations** (consolidated):
- `spinlock.c` - Primary ticket spinlock with exponential backoff
- `sleeplock.c` - Sleeping locks for I/O operations
- `rcu.c` - Read-Copy-Update for read-heavy workloads
- `modern_locks.c` - MCS, CLH, and advanced lock types
- Legacy implementations archived in `kernel/sync/legacy/`

**LibOS** (`libos/` - organized by function):
```
libos/
├── posix/       # POSIX API layer (posix.c)
├── pthread/     # Threading (pthread_core.c, pthread_mutex.c)
├── signal/      # Signal handling (signal_posix.c)
├── fs/          # File operations (fs.c, fs_ext.c, file.c)
├── mem/         # Memory operations (memory.c)
└── (core files in root: errno.c, env.c, process.c, time.c, user.c)
```

**User Programs** (`user/` - deduplicated):
- Core utilities consolidated from variants (_working, _real, _simple)
- Standard POSIX utilities: cat, echo, ls, cp, mv, pwd, test, sh
- File operations: mkdir, rm, chmod, ln, touch, dd
- Process tools: ps, kill, nice, renice
- System utilities: init, date, uname, whoami

## CMake Configuration Options

```cmake
# Build type
-DCMAKE_BUILD_TYPE=Release|Debug

# Feature flags
-DUSE_TICKET_LOCK=ON|OFF     # Ticket spinlocks
-DUSE_CAPNP=ON|OFF           # Cap'n Proto support
-DUSE_SIMD=ON|OFF            # SIMD optimizations
-DIPC_DEBUG=ON|OFF           # IPC debugging
-DCONFIG_SMP=ON|OFF          # Multi-core support
```

## Project Structure

### Build System
```
CMakeLists.txt      # Main CMake configuration (C17, native build)
build/              # Out-of-source build directory
  ├── bin/          # Executables
  ├── lib/          # Libraries
  ├── obj/          # Object files
  └── fs/           # Filesystem staging
include/       # Public headers
src/arch/      # Architecture-specific code
demos/         # Example programs
proto/         # Cap'n Proto schemas
tests/         # Test suite
scripts/       # Build and utility scripts
docs/          # Documentation
```

### Key Files
- `CMakeLists.txt` - Main CMake configuration
- `kernel.ld` - Kernel linker script
- `mkfs.c` - File system image creator
- `bootasm.S` - Boot assembly code
- `bootmain.c` - Boot C code

## Code Standards

- **Language**: C17 (`-std=c17`)
- **POSIX**: `_POSIX_C_SOURCE=200809L`
- **Compiler**: Native Clang/GCC (no cross-compiler needed)
- **Style**: LLVM formatting via clang-format
- **Headers**: Include guards, no pragma once

## Common Tasks

### Add New User Program
```bash
# 1. Create program
vim user/newprog.c

# 2. Add to CMakeLists.txt USER_PROGRAMS list
# 3. Rebuild
cd build && cmake --build .
```

### Add Kernel Module
```bash
# 1. Create module
vim kernel/newmodule.c

# 2. Add to KERNEL_SOURCES in CMakeLists.txt
# 3. Rebuild kernel
cd build && cmake --build . --target kernel.elf
```

### Debug Kernel Panic
```bash
# 1. Run with GDB
cmake --build . --target qemu-gdb

# 2. In another terminal
gdb kernel.elf
(gdb) target remote :26000
(gdb) break panic
(gdb) continue
```

## Performance Targets

- IPC latency: < 1000 cycles
- Context switch: < 2000 cycles  
- Capability check: < 100 cycles
- Boot time: < 1 second
- Kernel size: < 500KB

## POSIX Compliance

### Implemented
- 133 errno codes
- 31+ signals  
- Full pthreads
- 17+ core utilities

### Standards Location
- SUSv5 specs: `/Users/eirikr/Library/Mobile Documents/com~apple~CloudDocs/_ORGANIZED_KINDA/Technical-Documentation/Standards/POSIX/susv5/`

## Known Issues

1. **Code Duplication**: 227 user programs with many `_real`, `_simple`, `_working` variants
   - Solution: Run `./scripts/deduplicate_utilities.sh`

2. **Multiple Spinlocks**: 5 different spinlock implementations need consolidation
   - Files: `spinlock.c`, `qspinlock.c`, `rspinlock.c`, `modern_locks.c`, `rcu.c`

3. **Build Warnings**: Some implicit function declarations
   - Fix: Add proper headers and prototypes

4. **Test Coverage**: Limited unit tests
   - Add more tests in `tests/` directory

## Development Workflow

### Standard Development Cycle
```bash
# 1. Configure
mkdir build && cd build
cmake .. -DCMAKE_BUILD_TYPE=Debug

# 2. Build
cmake --build . -j$(nproc)

# 3. Test
ctest -V

# 4. Run
cmake --build . --target qemu

# 5. Debug if needed
cmake --build . --target qemu-gdb
```

### Before Committing
```bash
# Format code
cmake --build . --target format

# Run linter
cmake --build . --target lint

# Run tests
ctest -V

# Check POSIX compliance
cmake --build . --target posix-test
```

## Directory Purpose

- `kernel/` - Ring 0 exokernel core
- `libos/` - User-space POSIX implementation
- `user/` - POSIX utilities and programs
- `include/` - Shared headers
- `tests/` - Unit and integration tests
- `scripts/` - Automation scripts
- `demos/` - Example programs
- `docs/` - Documentation
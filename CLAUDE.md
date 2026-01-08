# FeuerBird Exokernel - Project Guidelines

## Overview

FeuerBird is a **full exokernel operating system** with libOSes, rump kernels, and DDEKit.
This is NOT a toy/stub kernel - it comprises ~180,000 LOC across 524 kernel files.

**Architecture**: Capability-based secure multiplexing with 17 subsystems
**Target Platforms**: x86_64 (primary), AArch64, ARM, PowerPC, MCU
**LibOS Personalities**: POSIX 2024 (SUSv5), Linux, BSD, Illumos, V6/V7 UNIX

## Build Instructions

### Quick Start (CMake + Ninja)

```bash
# Configure
cmake -B build -G Ninja -DCMAKE_BUILD_TYPE=Debug

# Build kernel
ninja -C build kernel

# Build everything
ninja -C build
```

### Conan 2 (Reproducible Builds)

```bash
# Install dependencies (from lockfile)
conan install . --output-folder=build --build=missing

# Cross-compile for freestanding kernel
conan install . -pr:h profiles/x86_64-freestanding --output-folder=build

# Regenerate lockfile after dependency changes
conan lock create .
```

### Build Profiles

| Profile | Purpose |
|---------|---------|
| `profiles/default` | Host development build (Debug, clang) |
| `profiles/x86_64-freestanding` | Kernel cross-compile (Release+LTO) |
| `profiles/aarch64-freestanding` | ARM64 kernel build |

### Build Options

```bash
cmake -B build -G Ninja \
  -DCMAKE_BUILD_TYPE=Release \
  -DUSE_CAPNP=ON \
  -DUSE_SIMD=ON \
  -DUSE_TICKET_LOCK=ON
```

## Standards

### Naming Convention

All targets use `feuerbird-*` prefix. See `docs/NAMING_CONVENTIONS.md` for details.

```cmake
feuerbird_add_executable(my-tool SOURCES main.c DEPENDENCIES feuerbird-architecture)
feuerbird_add_library(feuerbird-my-lib STATIC SOURCES lib.c)
```

**Deprecated**: `phoenix_*` / `phoenix-*` - do NOT use in new code.

### C Code Style

- Lowercase with underscores: `capability_table.c`
- Prefix conventions: `exo_` (exokernel), `cap_` (capability), `ipc_` (IPC)
- Header guards: `FEUERBIRD_<COMPONENT>_<FILE>_H`
- Types: `_t` suffix for typedefs (`cap_id_t`, `proc_t`)

### Quality Gates

- Treat warnings as errors: `-Wall -Wextra -Werror`
- No floating-point in kernel (use Q16.16 fixed-point)
- Run `shellcheck` on shell scripts
- Verify builds: `ninja -C build && ninja -C build test`

## Architecture

### Directory Structure

```
kernel/           # Exokernel (Ring 0) - 524 files
  sync/           # Synchronization primitives
  sched/          # Scheduler implementations
  ipc/            # Inter-process communication
  capability/     # Capability system
  boot/           # Boot infrastructure
libos/            # Library OS layer (Ring 3+)
user/             # Userspace utilities (214 tools)
src/arch/         # Architecture-specific code
  x64/            # x86_64 implementation
  aarch64/        # ARM64 implementation
  mcu/            # Microcontroller support
ddekit/           # L4-derived device driver kit
formal/           # Coq proofs and TLA+ specs
docs/             # Documentation
```

### Canonical Implementations

| Component | Canonical | Location |
|-----------|-----------|----------|
| IPC | Classic xv6 | `kernel/ipc/cap.c` |
| Capabilities | Exokernel Cap | `kernel/cap.c` |
| Spinlock | Classic | `kernel/spinlock.c` |
| Sleep lock | Classic | `kernel/sleeplock.c` |
| Ticket lock | Optional | `kernel/ticketlock.c` |

**Experimental/Archived**: quantum_ipc, lattice_ipc, unified_channel, genetic_lock, quantum_lock

## Current Status (January 2025)

### Working

- Kernel builds successfully as 64-bit ELF
- Conan 2 integration with lockfile
- CMake build system with feuerbird-* targets
- Architecture abstraction layer

### In Progress

- **QEMU Boot**: Multiboot2 header created (`src/arch/x64/multiboot2.S`) but blocked
  on linker script refactoring. See `docs/QEMU_BOOT_STATUS.md`.

### Known Issues

1. **Multiboot2 blocked**: Requires low-memory boot section in `kernel/kernel.ld`
2. **lambda_cap.c excluded**: Linker issues (cap_revoke, cap_table_remove undefined)
3. **q16_octonion.c excluded**: Requires SIMD detection infrastructure

## Common Tasks

### Adding a Kernel Module

```cmake
# In kernel/CMakeLists.txt
feuerbird_add_library(feuerbird-kernel-mymodule
    STATIC
    SOURCES mymodule.c
    INCLUDES ${CMAKE_CURRENT_SOURCE_DIR}/include
    DEPENDENCIES feuerbird-architecture
)
target_link_libraries(kernel PRIVATE feuerbird-kernel-mymodule)
```

### Testing QEMU Boot

```bash
# Current workaround (GRUB2 disk image)
grub-mkrescue -o feuerbird.iso iso/
qemu-system-x86_64 -cdrom feuerbird.iso

# Direct boot (blocked - see docs/QEMU_BOOT_STATUS.md)
# qemu-system-x86_64 -kernel build/kernel/kernel
```

### Running Formal Verification

```bash
# Coq proofs
make -C formal/coq

# TLA+ model checking
tlc formal/tla/ExoCap.tla
```

## Troubleshooting

### Build Fails with "undefined reference"

Check if the file is excluded in `kernel/CMakeLists.txt`. Many experimental
files are filtered out due to type conflicts or missing dependencies.

### "phoenix" references in error messages

Legacy naming. Check `cmake/FeuerBirdConfig.cmake` - aliases exist for
backwards compatibility but should not be used in new code.

### Linker relocation errors in boot code

32-bit boot code cannot reference high-half kernel addresses. Boot
infrastructure needs `.boot` section at physical address 0x100000.

## References

- @./docs/ARCHITECTURAL_OVERVIEW.md - Full system architecture
- @./docs/NAMING_CONVENTIONS.md - Naming standards
- @./docs/QEMU_BOOT_STATUS.md - Boot infrastructure status
- @./docs/REPOSITORY_ORGANIZATION.md - Directory layout
- @./formal/ - Coq proofs and TLA+ specifications

# FeuerBird Exokernel

[![C17](https://img.shields.io/badge/C-17-blue.svg)](https://en.wikipedia.org/wiki/C17_(C_standard_revision))
[![POSIX.1-2024](https://img.shields.io/badge/POSIX-2024-green.svg)](https://pubs.opengroup.org/onlinepubs/9799919799/)
[![License](https://img.shields.io/badge/License-MIT-yellow.svg)](LICENSE)
[![Architecture](https://img.shields.io/badge/Arch-x86__64%20%7C%20AArch64-orange.svg)]()

An exokernel operating system focused on POSIX 2024 (SUSv5) compliance, capability-based security, and multi-personality Unix compatibility. Derived from the MIT PDOS xv6 teaching kernel.

## Overview

FeuerBird implements a three-zone exokernel architecture that separates mechanism from policy:

- **Exokernel Zone (Ring 0)**: Minimal kernel providing secure resource multiplexing and capability management
- **LibOS Zone**: POSIX, Linux, BSD, and Plan 9 compatibility layers
- **Application Zone**: User utilities and applications

```
┌─────────────────────────────────────────────────────────────┐
│                   APPLICATION ZONE (Ring 3)                 │
│  User Applications │ POSIX Utilities │ Custom Applications  │
├─────────────────────────────────────────────────────────────┤
│                    LIBOS ZONE (Ring 3+)                     │
│  POSIX LibOS │ Plan9 LibOS │ Linux Compat │ BSD Compat     │
├─────────────────────────────────────────────────────────────┤
│                   EXOKERNEL ZONE (Ring 0)                   │
│  Secure Multiplex │ Capability System │ IPC │ HAL          │
└─────────────────────────────────────────────────────────────┘
```

## Project Statistics

| Metric | Count |
|--------|-------|
| C source files | 524 |
| Header files | 271 |
| Lines of C code | ~93,000 |
| Lines of headers | ~24,000 |
| User utilities | 214 |
| Python tests | 65 |
| Documentation files | 202 |
| Shell scripts | 38 |

## Quick Start

### Using Docker (Recommended)

```bash
git clone https://github.com/Oichkatzelesfrettschen/feuerbird_exokernel.git
cd feuerbird_exokernel

# Build container
./scripts/docker-build.sh build

# Build kernel
./scripts/docker-build.sh cmake Release

# Interactive shell
./scripts/docker-build.sh shell
```

See [docs/CONTAINER_BUILD.md](docs/CONTAINER_BUILD.md) for details.

### Native Build

**Requirements**: Clang 15+ or GCC 11+ (C17), CMake 3.16+, Ninja, Python 3.8+, QEMU 7.0+

```bash
git clone https://github.com/Oichkatzelesfrettschen/feuerbird_exokernel.git
cd feuerbird_exokernel

mkdir build && cd build
cmake .. -GNinja -DCMAKE_BUILD_TYPE=Debug
ninja

# Run in QEMU
ninja qemu-nox
```

### Build Options

```bash
# LTO and optimizations
cmake .. -DUSE_LTO=ON -DUSE_LLD=ON -DUSE_POLLY=ON

# Sanitizers
cmake .. -DENABLE_ASAN=ON -DENABLE_UBSAN=ON

# Cross-compilation
cmake .. -DCMAKE_TOOLCHAIN_FILE=../cmake/toolchain-x86_64.cmake
```

## Directory Structure

```
feuerbird_exokernel/
├── kernel/         # Exokernel core (syscalls, IPC, capabilities, scheduling)
├── libos/          # Library OS layer (POSIX, pthread, filesystem abstractions)
├── user/           # 214 user-space utilities (cat, ls, sh, grep, etc.)
├── include/        # Public headers
├── src/            # Architecture and HAL implementations
├── tests/          # Test suite (C and Python)
├── docs/           # Documentation (202 files)
├── tools/          # Development tools
├── scripts/        # Build and automation scripts
├── formal/         # TLA+ formal specifications
└── proto/          # Protocol definitions (Cap'n Proto)
```

## Key Features

### Multi-Personality System Calls

Supports binaries from multiple Unix variants through a syscall gateway:

- **POSIX 2024 (SUSv5)** - Native personality
- **Linux** - Syscall emulation layer
- **BSD** - FreeBSD/OpenBSD compatibility
- **illumos** - Doors IPC, zones
- **Historical Unix** - V6/V7 support

See [docs/ARCHITECTURAL_OVERVIEW.md](docs/ARCHITECTURAL_OVERVIEW.md).

### Capability-Based Security

```c
typedef struct capability {
    cap_id_t id;           // 16-bit unique identifier
    cap_type_t type;       // Resource type
    uint32_t permissions;  // Access rights
    uint64_t auth_token;   // FNV-1a authentication hash
    void *resource;        // Resource pointer
    uint32_t ref_count;    // Reference counting
} capability_t;
```

- 65,536 capability slots
- Cryptographic authentication
- Delegation with permission reduction
- Cascading revocation

See [docs/CAPABILITY_MODEL.md](docs/CAPABILITY_MODEL.md).

### Scheduling

- Beatty sequence scheduler (golden ratio fairness)
- DAG task scheduler with dependency resolution
- Real-time scheduling support

### IPC

- Zero-copy message passing
- Typed channels
- Gas accounting for DoS prevention
- Cap'n Proto support

## User Utilities

214 utilities in `user/` including:

- **Core**: cat, ls, mkdir, rm, cp, mv, ln, pwd, echo, sh
- **Text**: grep, sed, awk, diff, sort, uniq, cut, head, tail, wc
- **Process**: ps, kill, nice, nohup, timeout, top, htop
- **Archive**: tar, zip, unzip, gzip, compress
- **Network**: curl, wget, ping, netstat, ifconfig
- **Development**: make, gcc, gdb, strace, valgrind

## Current Status

Per [docs/PROJECT_STATUS_2025.md](docs/PROJECT_STATUS_2025.md):

### Implemented
- Core exokernel with capability system
- Basic POSIX syscalls and signal handling
- pthread support
- File operations
- ~60 functional POSIX utilities

### In Progress
- Full POSIX 2024 compliance
- Network stack
- Complete Linux binary compatibility
- Additional utilities (target: 150)

### Roadmap 2025
- Q1: Core completion, security audit
- Q2: Full Linux/BSD compatibility
- Q3: Production hardening
- Q4: 1.0 release

## Testing

```bash
# Python tests
pytest tests/

# C tests (via CMake)
ninja -C build test

# POSIX compliance tests
./scripts/run_posix_tests.sh
```

## Documentation

Key documents in `docs/`:

- [PROJECT_STATUS_2025.md](docs/PROJECT_STATUS_2025.md) - Current status
- [ARCHITECTURAL_OVERVIEW.md](docs/ARCHITECTURAL_OVERVIEW.md) - Multi-personality architecture
- [CAPABILITY_MODEL.md](docs/CAPABILITY_MODEL.md) - Security model
- [CONTAINER_BUILD.md](docs/CONTAINER_BUILD.md) - Docker build guide
- [ROADMAP_2025.md](docs/ROADMAP_2025.md) - Development roadmap

## Contributing

1. Fork the repository
2. Create a feature branch
3. Follow C17 standards and project coding style (see `.clang-format`)
4. Test with the provided test suite
5. Submit a pull request

## License

MIT License - derived from MIT PDOS xv6 teaching kernel.

```
Original: Copyright (c) 2006-2018 Frans Kaashoek, Robert Morris, Russ Cox, MIT
FeuerBird: Copyright (c) 2024 FeuerBird Project
```

See [LICENSE](LICENSE) for full text.

## Links

- **Issues**: [GitHub Issues](https://github.com/Oichkatzelesfrettschen/feuerbird_exokernel/issues)
- **Discussions**: [GitHub Discussions](https://github.com/Oichkatzelesfrettschen/feuerbird_exokernel/discussions)

---

*Note: The original comprehensive README is preserved in [README.old.md](README.old.md).*
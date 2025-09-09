# OpenAI Codex Instructions

**This file provides guidance to OpenAI Codex when working with the FeuerBird Exokernel codebase.**

## 📖 Primary Documentation

**All project information is consolidated in [README.md](README.md) - the definitive source of truth.**

## 🎯 Project Context

FeuerBird is a research-grade exokernel operating system with:
- **POSIX-2024 (SUSv5) Full Compliance** - All 131 mandatory utilities implemented
- **Pure C17 Codebase** - Modern language standards throughout
- **Capability-Based Security** - Mathematical security guarantees  
- **High-Performance IPC** - Sub-1000 cycle latency targets
- **Multi-Architecture** - Native x86_64 and AArch64 support

**➡️ See [README.md](README.md) for comprehensive details**

## 🛠️ Build System & Workflow

### CMake Configuration
```bash
# Standard build
mkdir build && cd build
cmake .. -DCMAKE_BUILD_TYPE=Release -DARCH=x86_64
cmake --build . -j$(nproc)

# Development build with debugging
cmake .. -DCMAKE_BUILD_TYPE=Debug \
         -DUSE_TICKET_LOCK=ON \
         -DIPC_DEBUG=ON
```

### Testing & Validation
```bash
ctest -V                              # Full test suite
cmake --build . --target posix-test   # POSIX compliance
cmake --build . --target format lint  # Code quality
```

## 🏗️ Architecture Overview

### Three-Zone Model
```
┌─────────────────────────────────────┐
│      Application Zone (Ring 3)      │  ← Unix programs, user apps
└─────────────────────────────────────┘
              ↕ Capabilities
┌─────────────────────────────────────┐
│   LibOS Zone (Ring 3, Privileged)   │  ← POSIX implementation
└─────────────────────────────────────┘
              ↕ Secure Bindings  
┌─────────────────────────────────────┐
│       Kernel Zone (Ring 0)          │  ← Hardware multiplexing
└─────────────────────────────────────┘
```

### Repository Structure  
```
src/
├── kernel/     # Kernel Zone - hardware multiplexing
├── libos/      # LibOS Zone - POSIX services  
├── user/       # Application Zone - utilities
├── arch/       # Architecture-specific code
└── hal/        # Hardware Abstraction Layer
```

## ⚡ Performance Requirements

Critical performance targets (see README.md for details):
- **IPC Latency**: < 1,000 cycles (zero-copy operations)
- **Context Switch**: < 2,000 cycles (optimized register saves)
- **Capability Check**: < 100 cycles (hardware acceleration)
- **Boot Time**: < 1 second (parallel initialization)

## 🔧 Code Generation Standards

### Language Requirements
- **Pure C17**: Use ISO C17 standard exclusively
  - `_Static_assert` for compile-time checks
  - `_Alignas` for cache-line alignment  
  - `stdatomic.h` for lock-free programming
  - `stdbool.h` for boolean types
  
### POSIX Compliance
- **SUSv5 Specification**: Strict adherence required
- **Error Handling**: Complete errno implementation (133 codes)
- **Signal Support**: Full POSIX signal handling (31+ signals)
- **Thread Safety**: pthreads compatibility

### Security Model
- **Capability-Based**: All access through capabilities
- **Zone Isolation**: Respect Kernel/LibOS/Application boundaries
- **Input Validation**: Validate all cross-zone communication
- **Secure Coding**: Use C17 safety features

## 🧪 Testing Protocol

### Required Testing
```bash
# Unit tests for all new code
cmake --build . --target unit-tests

# POSIX compliance verification
cmake --build . --target posix-test

# Performance regression testing  
cmake --build . --target stress-tests

# Multi-architecture validation
cmake .. -DARCH=aarch64 && cmake --build .
```

### Code Quality
```bash
# Automatic formatting
cmake --build . --target format

# Static analysis  
cmake --build . --target lint analyze

# Memory safety (AddressSanitizer)
cmake .. -DCMAKE_C_FLAGS="-fsanitize=address"
```

## 🚀 Common Development Tasks

### Emulation & Debugging
```bash
# Run in QEMU
cmake --build . --target qemu

# Debug with GDB
cmake --build . --target qemu-gdb
gdb kernel.elf -ex "target remote :26000"
```

### Architecture Targets
```bash
# x86_64 (Intel/AMD)
cmake .. -DARCH=x86_64

# AArch64 (Apple Silicon, ARM64)  
cmake .. -DARCH=aarch64
```

## 📋 Modification Guidelines

### When Generating Code
1. **Read README.md first** - Understand current architecture
2. **Maintain zone boundaries** - Respect security model
3. **Use modern C17** - No legacy C constructs
4. **Include tests** - All new functionality must be tested
5. **Document thoroughly** - Doxygen-style comments required

### Change Process
1. **Analyze existing patterns** in similar files
2. **Follow naming conventions** from codebase
3. **Preserve performance** - No degradation of metrics
4. **Update documentation** - Keep README.md current
5. **Validate thoroughly** - Run full test suite

## 🎯 Priority Areas

High-value code generation opportunities:
- **POSIX Utility Implementation** - Completing missing utilities
- **Performance Optimization** - Assembly critical paths
- **C17 Modernization** - Converting legacy code
- **Test Coverage** - Expanding test suite
- **HAL Implementation** - Hardware abstraction layers

## 📚 Documentation References

**Primary Sources** (in priority order):
1. **[README.md](README.md)** ← **MAIN REFERENCE** (comprehensive)
2. **[CONTRIBUTING.md](CONTRIBUTING.md)** ← Development guidelines
3. **Source Code** ← Implementation patterns and conventions
4. **[docs/](docs/)** ← Detailed technical documentation

---

**For complete project information, refer to [README.md](README.md) - the canonical documentation containing all architecture, build, testing, and development details.**
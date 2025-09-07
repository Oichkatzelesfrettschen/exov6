# Claude Code Instructions

**This file provides guidance to Claude Code (claude.ai/code) when working with this repository.**

## 📖 Primary Documentation

**All comprehensive project information is located in [README.md](README.md) - the canonical source of truth.**

## 🎯 Project Overview

FeuerBird is a POSIX-2024 (SUSv5) compliant exokernel operating system written in pure C17. See [README.md](README.md) for complete details on:

- **Three-Zone Architecture**: Kernel/LibOS/Application separation  
- **Capability-Based Security**: 65,536 slots with HMAC-SHA256
- **Multi-Architecture Support**: x86_64 and AArch64
- **Advanced IPC System**: Zero-copy with sub-1000 cycle latency
- **Complete POSIX Compliance**: All 131 mandatory utilities

## 🛠️ Development Workflow

### Build System (CMake)
```bash
# Basic build
mkdir build && cd build
cmake .. -DCMAKE_BUILD_TYPE=Release -DARCH=x86_64
cmake --build . -j$(nproc)

# With debugging and features
cmake .. -DCMAKE_BUILD_TYPE=Debug \
         -DUSE_TICKET_LOCK=ON \
         -DIPC_DEBUG=ON \
         -DCONFIG_SMP=ON
```

### Testing & Quality
```bash
# Complete test suite
ctest -V

# POSIX compliance testing  
cmake --build . --target posix-test

# Code quality checks
cmake --build . --target format lint analyze
```

### QEMU Emulation
```bash
cmake --build . --target qemu        # Run with graphics
cmake --build . --target qemu-nox    # Run headless
cmake --build . --target qemu-gdb    # Debug with GDB
```

## 🔧 Critical Requirements

### Code Standards (MUST FOLLOW)
- **Pure C17**: ALL code must use ISO C17 standard with modern features
- **POSIX-2024**: Strict SUSv5 specification compliance
- **Multi-Architecture**: Platform-agnostic with HAL abstraction
- **Performance First**: Maintain target metrics (see README.md)
- **Security Model**: Preserve capability-based architecture

### Repository Structure
```
src/              # Source code (organized by function)
├── kernel/       # Kernel Zone (Ring 0) 
├── libos/        # LibOS Zone (Ring 3, Privileged)
├── user/         # Application Zone (Ring 3, User)
├── arch/         # Architecture-specific code
└── hal/          # Hardware Abstraction Layer

include/          # Headers (mirrors src/ structure)
tests/            # Comprehensive test suite
tools/            # Build and development tools
docs/             # Documentation by topic
```

### Performance Targets
Maintain these metrics from README.md:
- **IPC Latency**: < 1,000 cycles
- **Context Switch**: < 2,000 cycles  
- **Capability Validation**: < 100 cycles
- **Boot Time**: < 1 second

## ⚠️ Important Notes

### When Making Changes
1. **Read README.md first** for current project status
2. **Preserve architecture boundaries** between zones
3. **Run full test suite** before and after changes
4. **Update README.md** for significant modifications
5. **Maintain POSIX compliance** for all utilities

### Code Modernization
- Convert legacy code to C17 during modification
- Use modern C17 features: `_Static_assert`, `_Alignas`, `stdatomic.h`
- Minimize assembly code (isolate in `src/arch/`)
- Follow HAL patterns for hardware access

### Testing Requirements
- Unit tests for all new functionality
- POSIX compliance verification
- Performance regression testing
- Multi-architecture validation

## 🚀 Quick Commands Reference

**Essential Operations:**
```bash
# Build and test
cmake --build . && ctest -V

# Format and lint
cmake --build . --target format lint

# Run system
cmake --build . --target qemu

# Debug kernel
cmake --build . --target qemu-gdb
gdb kernel.elf -ex "target remote :26000"
```

**Architecture Targets:**
```bash
# x86_64 (default)
cmake .. -DARCH=x86_64

# AArch64/Apple Silicon
cmake .. -DARCH=aarch64
```

## 📚 Additional Documentation

For detailed information beyond this summary, see:

- **[README.md](README.md)** - Complete project documentation (PRIMARY)
- **[CONTRIBUTING.md](CONTRIBUTING.md)** - Contribution guidelines  
- **[docs/](docs/)** - Topic-specific documentation

## 🔄 Update Protocol

When significant changes are made:
1. Update README.md with new information
2. Ensure all documentation remains consistent  
3. Update build configuration if needed
4. Add comprehensive tests for new features
5. Verify POSIX compliance is maintained

---

**For complete information, refer to [README.md](README.md) - the authoritative project documentation.**
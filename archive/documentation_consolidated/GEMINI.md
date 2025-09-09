# Gemini AI Instructions

**This file provides guidance to Google Gemini AI when working with the FeuerBird Exokernel project.**

## 📖 Canonical Documentation

**All project information is unified in [README.md](README.md) - the single source of truth for this repository.**

## 🎯 Project Summary

FeuerBird is an advanced exokernel operating system featuring:
- **Pure C17 Implementation** with modern language standards
- **POSIX-2024 (SUSv5) Compliance** with all 131 mandatory utilities  
- **Capability-Based Security** with mathematical guarantees
- **Three-Zone Architecture** separating mechanism from policy
- **Multi-Architecture Support** for x86_64 and AArch64
- **High-Performance IPC** with zero-copy operations

**➡️ Complete details available in [README.md](README.md)**

## 🛠️ Key Development Information

### Build System
The project uses **CMake** as the primary build system:
```bash
mkdir build && cd build
cmake .. -DCMAKE_BUILD_TYPE=Release
cmake --build . -j$(nproc)
ctest -V
```

### Architecture
```
Application Zone (Ring 3, User)
         ↕ Capabilities
LibOS Zone (Ring 3, Privileged) 
         ↕ Secure Bindings
Kernel Zone (Ring 0, Native)
```

### Repository Organization
- `src/` - Source code organized by function
- `include/` - Header files mirroring src structure
- `tests/` - Comprehensive test suite
- `docs/` - Topic-specific documentation
- `tools/` - Build and development utilities

## ⚡ Performance Targets

Critical metrics to maintain (from README.md):
- **IPC Latency**: < 1,000 cycles
- **Context Switch**: < 2,000 cycles
- **Capability Validation**: < 100 cycles  
- **Boot Time**: < 1 second

## 🔧 Development Standards

### Code Requirements
- **Pure C17**: All code must use ISO C17 standard
- **POSIX-2024**: Strict adherence to SUSv5 specification
- **Security First**: Maintain capability-based security model
- **Multi-Architecture**: Platform-agnostic design with HAL
- **Performance Focused**: No degradation of target metrics

### Testing Protocol
- Run full test suite: `ctest -V`
- POSIX compliance: `cmake --build . --target posix-test`
- Code quality: `cmake --build . --target format lint analyze`
- Multi-architecture validation required

## 🚀 Quick Reference Commands

**Essential Operations:**
```bash
# Build and test
cmake --build . && ctest -V

# QEMU emulation
cmake --build . --target qemu

# Debug with GDB  
cmake --build . --target qemu-gdb
```

**Architecture Selection:**
```bash
cmake .. -DARCH=x86_64    # Intel/AMD (default)
cmake .. -DARCH=aarch64   # ARM64/Apple Silicon
```

## 📋 Change Management

For any modifications:
1. **Consult README.md first** for current project status
2. **Maintain zone boundaries** in three-zone architecture
3. **Preserve POSIX compliance** for all utilities
4. **Update README.md** for significant changes
5. **Run comprehensive tests** before and after changes

## 🎯 Focus Areas

Key areas for AI assistance:
- **C17 Modernization**: Converting legacy code to modern standards
- **POSIX Compliance**: Implementing and testing utility functions
- **Performance Optimization**: Achieving target cycle counts
- **Security Enhancement**: Strengthening capability-based model
- **Documentation**: Maintaining consistency with README.md

## 📚 Documentation Hierarchy

1. **[README.md](README.md)** ← **PRIMARY SOURCE** (comprehensive)
2. **[CONTRIBUTING.md](CONTRIBUTING.md)** ← Contribution guidelines
3. **[docs/](docs/)** ← Topic-specific documentation
4. **Agent files** (AGENTS.md, CLAUDE.md, etc.) ← AI-specific pointers

---

**For complete project information, architecture details, build instructions, and development guidelines, see [README.md](README.md) - the authoritative documentation.**
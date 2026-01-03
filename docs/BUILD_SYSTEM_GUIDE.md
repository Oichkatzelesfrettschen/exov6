# FeuerBird Exokernel - Build System & Tooling Guide

## Table of Contents

1. [Overview](#overview)
2. [Build Systems](#build-systems)
3. [Static Analysis Tools](#static-analysis-tools)
4. [Code Coverage](#code-coverage)
5. [Development Container](#development-container)
6. [CI/CD Pipeline](#cicd-pipeline)
7. [Build Optimization](#build-optimization)
8. [Troubleshooting](#troubleshooting)

---

## Overview

FeuerBird Exokernel uses a comprehensive, modern build infrastructure designed for:

- **Multi-system support**: CMake (primary) and Meson (legacy)
- **LLVM toolchain**: Clang 18, LLD linker, ThinLTO, Polly optimizations
- **Static analysis**: clang-tidy, cppcheck, include-what-you-use
- **Code coverage**: LLVM coverage (llvm-cov) and GCC coverage (gcov/lcov)
- **Fast rebuilds**: ccache integration
- **Containerized development**: Docker and Dev Containers
- **Automated CI/CD**: GitHub Actions with matrix builds

---

## Build Systems

### CMake (Primary)

CMake is the primary build system with comprehensive feature support.

#### Quick Start

```bash
# Standard build
cmake -B build -G Ninja -DCMAKE_BUILD_TYPE=Debug
ninja -C build

# Run in QEMU
ninja -C build qemu-nox
```

#### Build Types

- **Debug**: Full debug info, no optimization (`-g -O0`)
- **Release**: Maximum optimization (`-O3 -DNDEBUG`)
- **RelWithDebInfo**: Optimized with debug info (`-O2 -g`)
- **MinSizeRel**: Size optimization (`-Os -DNDEBUG`)

#### Build Options

**Core Features:**
```bash
-DUSE_LTO=ON              # Enable ThinLTO optimization
-DUSE_LLD=ON              # Use LLVM LLD linker
-DUSE_POLLY=ON            # Enable Polly loop optimizations
-DUSE_SIMD=ON             # Enable SIMD instructions
```

**Sanitizers:**
```bash
-DENABLE_ASAN=ON          # AddressSanitizer
-DENABLE_UBSAN=ON         # UndefinedBehaviorSanitizer
-DENABLE_TSAN=ON          # ThreadSanitizer
-DENABLE_MSAN=ON          # MemorySanitizer
```

**Analysis & Coverage:**
```bash
-DENABLE_COVERAGE=ON      # Code coverage instrumentation
-DENABLE_STATIC_ANALYSIS=ON   # All static analysis tools
-DENABLE_CLANG_TIDY=ON    # clang-tidy during build
-DENABLE_CPPCHECK=ON      # cppcheck analysis
-DENABLE_IWYU=ON          # include-what-you-use
-DENABLE_CCACHE=ON        # ccache (enabled by default)
```

**Components:**
```bash
-DBUILD_DEMOS=ON          # Build demo programs
-DBUILD_TESTS=ON          # Build test suite
-DBUILD_TOOLS=ON          # Build development tools
-DBUILD_DOCS=ON           # Build documentation
```

#### Example Configurations

**Development Build:**
```bash
cmake -B build -G Ninja \
  -DCMAKE_BUILD_TYPE=Debug \
  -DENABLE_ASAN=ON \
  -DENABLE_UBSAN=ON \
  -DENABLE_COVERAGE=ON \
  -DENABLE_STATIC_ANALYSIS=ON
```

**Production Build:**
```bash
cmake -B build -G Ninja \
  -DCMAKE_BUILD_TYPE=Release \
  -DUSE_LTO=ON \
  -DUSE_LLD=ON \
  -DUSE_POLLY=ON
```

**Testing Build:**
```bash
cmake -B build -G Ninja \
  -DCMAKE_BUILD_TYPE=Debug \
  -DENABLE_COVERAGE=ON \
  -DBUILD_TESTS=ON
```

### Meson (Legacy)

Meson is maintained for compatibility but has fewer features.

```bash
# Basic build
meson setup builddir
ninja -C builddir

# With options
meson setup builddir -Duse_capnp=true -Dipc_debug=true
ninja -C builddir

# Run in QEMU
meson compile -C builddir qemu-nox
```

---

## Static Analysis Tools

FeuerBird integrates multiple static analysis tools for comprehensive code quality checks.

### clang-tidy

Comprehensive C/C++ linter with 300+ checks for:
- Bug detection
- Security vulnerabilities
- Performance issues
- Readability improvements
- Modernization suggestions

**Configuration:** `.clang-tidy`

**Usage:**
```bash
# During build (if ENABLE_CLANG_TIDY=ON)
ninja -C build

# Manual analysis
ninja -C build clang-tidy

# Analyze specific file
clang-tidy --config-file=.clang-tidy path/to/file.c
```

**Key Check Categories:**
- `bugprone-*`: Bug-prone code patterns
- `cert-*`: CERT secure coding standards
- `clang-analyzer-*`: Deep static analysis
- `concurrency-*`: Thread safety issues
- `performance-*`: Performance optimizations
- `readability-*`: Code clarity improvements

### cppcheck

Standalone static analyzer focusing on:
- Undefined behavior
- Memory leaks
- Buffer overflows
- Null pointer dereferences
- Uninitialized variables

**Usage:**
```bash
# Run cppcheck
ninja -C build cppcheck

# Text report
ninja -C build cppcheck-text

# View reports
cat build/cppcheck-report.txt
```

### include-what-you-use (IWYU)

Analyzes `#include` directives to:
- Remove unnecessary includes
- Add missing includes
- Use forward declarations

**Usage:**
```bash
# During build (if ENABLE_IWYU=ON)
ninja -C build

# Manual analysis
ninja -C build iwyu
```

### Unified Analysis

Run all static analysis tools:
```bash
cmake -B build -G Ninja -DENABLE_STATIC_ANALYSIS=ON
ninja -C build static-analysis
```

---

## Code Coverage

FeuerBird supports both LLVM and GCC coverage tools.

### LLVM Coverage (Clang)

**Enable:**
```bash
cmake -B build -G Ninja \
  -DCMAKE_BUILD_TYPE=Debug \
  -DENABLE_COVERAGE=ON
ninja -C build
```

**Generate Coverage:**
```bash
# Run tests to generate coverage data
ninja -C build test

# Generate coverage report
ninja -C build coverage

# View HTML report
firefox build/coverage/html/index.html
```

**Targets:**
- `coverage-clean`: Clean coverage data
- `coverage-merge`: Merge .profraw files
- `coverage-report`: Text coverage summary
- `coverage-html`: HTML coverage report
- `coverage`: Full coverage analysis

### GCC Coverage (GCC)

Same workflow, automatically detected when using GCC.

**Targets:**
- `coverage-clean`: Clean .gcda files
- `coverage-capture`: Capture coverage data
- `coverage-filter`: Filter system files
- `coverage-report`: Text coverage summary
- `coverage-html`: HTML coverage report
- `coverage`: Full coverage analysis

### Coverage Metrics

Coverage reports include:
- Line coverage: % of lines executed
- Function coverage: % of functions called
- Branch coverage: % of branches taken
- Region coverage: % of code regions executed

---

## Development Container

FeuerBird provides a complete development container with all tools pre-installed.

### Using Dev Container (VS Code)

1. Install VS Code and "Dev Containers" extension
2. Open project in VS Code
3. Press `F1` → "Dev Containers: Reopen in Container"
4. Container builds with all tools installed

**Features:**
- LLVM 18 toolchain (clang, lld, clang-tidy, clang-format)
- Static analysis tools (cppcheck, IWYU)
- Coverage tools (llvm-cov, gcov, lcov)
- Build systems (CMake, Ninja, Meson)
- QEMU for kernel testing
- Python tools (pytest, black, flake8)
- Debugging tools (gdb, valgrind, strace)
- ccache for fast rebuilds
- Pre-configured VS Code extensions

**Configuration:** `.devcontainer/devcontainer.json`

### Using Docker Directly

```bash
# Build container
docker build -f .devcontainer/Dockerfile -t feuerbird-dev .

# Run container
docker run -it -v $(pwd):/workspace feuerbird-dev

# Inside container
cd /workspace
cmake -B build -G Ninja
ninja -C build
```

### Container Features

- **User**: `vscode` (uid 1000)
- **Persistent volumes**: ccache, CMake cache
- **Privileged mode**: For QEMU and debugging
- **Pre-installed extensions**: C/C++, CMake Tools, Python, GitLens, etc.

---

## CI/CD Pipeline

GitHub Actions workflow provides comprehensive automated testing.

**Workflow:** `.github/workflows/feuerbird_ci.yml`

### Build Matrix

**Configurations:**
1. **Baseline Build**: Standard RelWithDebInfo build
2. **Modern LLVM**: LLD + ThinLTO + Polly optimizations
3. **Security**: AddressSanitizer enabled
4. **Development**: Debug with SIMD and IPC debug

**Architecture Matrix:**
- x86_64
- aarch64 (cross-compilation)

### CI Stages

1. **Pre-commit checks**: Linting, formatting (baseline only)
2. **Build**: Compile with matrix configurations
3. **Validation**: Verify build artifacts
4. **Unit tests**: Python pytest suite
5. **QEMU smoke test**: Quick kernel boot test
6. **Final validation**: Release build + metrics

### Manual CI Testing

```bash
# Run pre-commit checks locally
pre-commit run --all-files

# Simulate CI build
cmake -B build -G Ninja -DCMAKE_BUILD_TYPE=RelWithDebInfo
ninja -C build
pytest tests/
ninja -C build qemu-nox  # Press Ctrl+A, X to exit
```

---

## Build Optimization

### ccache

ccache is enabled by default and dramatically speeds up rebuilds.

**Targets:**
```bash
ninja -C build ccache-stats    # Show cache statistics
ninja -C build ccache-zero     # Reset statistics
ninja -C build ccache-clean    # Clear cache
ninja -C build ccache-info     # Detailed information
```

**Configuration:**
- Max cache size: 5GB
- Compression: enabled (level 6)
- Located: `~/.ccache` or `/home/vscode/.ccache` (container)

### Parallel Builds

```bash
# Use all CPU cores
ninja -C build -j $(nproc)

# Limit to 4 cores
ninja -C build -j4
```

### Incremental Builds

CMake tracks dependencies automatically. After changes:

```bash
# Rebuild only changed files
ninja -C build

# Rebuild specific target
ninja -C build kernel
```

### Link-Time Optimization (LTO)

```bash
cmake -B build -G Ninja \
  -DCMAKE_BUILD_TYPE=Release \
  -DUSE_LTO=ON \
  -DUSE_LLD=ON

ninja -C build
```

LTO provides:
- 10-20% size reduction
- 5-15% performance improvement
- Whole-program optimization

---

## Troubleshooting

### Build Fails with "Compiler not found"

**Problem:** CMake can't find clang compiler

**Solution:**
```bash
# Install LLVM toolchain
sudo apt-get install clang-18 lld-18

# Specify compiler explicitly
cmake -B build -G Ninja \
  -DCMAKE_C_COMPILER=clang-18 \
  -DCMAKE_CXX_COMPILER=clang++-18
```

### clang-tidy Too Slow

**Problem:** clang-tidy slows down builds significantly

**Solution:**
```bash
# Disable during build
cmake -B build -G Ninja -DENABLE_CLANG_TIDY=OFF

# Run manually when needed
ninja -C build clang-tidy
```

### Coverage Data Not Generated

**Problem:** No .profraw or .gcda files

**Solution:**
```bash
# Ensure coverage is enabled
cmake -B build -G Ninja -DENABLE_COVERAGE=ON
ninja -C build

# Run tests/kernel to generate data
ninja -C build test
# or
LLVM_PROFILE_FILE="build/default.profraw" ./build/kernel

# Then generate report
ninja -C build coverage
```

### ccache Not Working

**Problem:** Cache miss rate is 100%

**Solution:**
```bash
# Check ccache status
ninja -C build ccache-info

# Verify ccache is in use
ninja -C build -v | grep ccache

# Reset and rebuild
ninja -C build ccache-clean
ninja -C build clean
ninja -C build
```

### QEMU Hangs

**Problem:** `ninja qemu-nox` doesn't return

**Solution:**
- Press `Ctrl+A` then `X` to exit QEMU
- Use timeout: `timeout 30s ninja -C build qemu-nox`

### Dev Container Build Fails

**Problem:** Docker build fails or takes too long

**Solution:**
```bash
# Use BuildKit for faster builds
DOCKER_BUILDKIT=1 docker build \
  -f .devcontainer/Dockerfile \
  -t feuerbird-dev .

# Or use existing builder container
docker pull ghcr.io/oichkatzelesfrettschen/feuerbird-builder:latest
```

### Out of Disk Space

**Problem:** Build fills up disk

**Solution:**
```bash
# Clean build artifacts
ninja -C build clean

# Clean ccache
ninja -C build ccache-clean

# Remove old builds
rm -rf build build-* builddir

# Clean Python cache
find . -type d -name __pycache__ -exec rm -rf {} +
find . -type d -name .pytest_cache -exec rm -rf {} +
```

---

## Summary

FeuerBird's build infrastructure provides:

✅ **Modern toolchain**: LLVM 18, LTO, LLD, Polly  
✅ **Quality assurance**: clang-tidy, cppcheck, IWYU  
✅ **Test coverage**: LLVM/GCC coverage with HTML reports  
✅ **Fast rebuilds**: ccache integration  
✅ **Containerized dev**: Dev Container with all tools  
✅ **Automated testing**: GitHub Actions CI/CD  
✅ **Multiple sanitizers**: ASAN, UBSAN, TSAN, MSAN  
✅ **Comprehensive docs**: This guide + inline comments  

For more information, see:
- `CMakeLists.txt` - Main build configuration
- `cmake/*.cmake` - CMake modules
- `.devcontainer/` - Dev container configuration
- `.github/workflows/` - CI/CD pipelines
- `README.md` - Project overview

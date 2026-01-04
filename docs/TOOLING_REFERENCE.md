# FeuerBird Exokernel - Tooling & Analysis Infrastructure

## Overview

This document provides a complete reference for all development, analysis, and automation tools integrated into the FeuerBird Exokernel project.

---

## 🛠️ Development Tools

### Compilers & Toolchains

| Tool | Version | Purpose | Configuration |
|------|---------|---------|---------------|
| **Clang** | 18+ | Primary C/C++ compiler | `CC=clang` |
| **GCC** | 11+ | Alternative compiler | `CC=gcc` |
| **LLD** | 18+ | LLVM linker (fast linking) | `-DUSE_LLD=ON` |
| **ThinLTO** | LLVM 18 | Link-time optimization | `-DUSE_LTO=ON` |
| **Polly** | LLVM 18 | Loop optimization | `-DUSE_POLLY=ON` |

### Build Systems

| Tool | Version | Purpose | Usage |
|------|---------|---------|-------|
| **CMake** | 3.16+ | Primary build system | `cmake -B build -G Ninja` |
| **Ninja** | 1.10+ | Build executor | `ninja -C build` |
| **Meson** | 1.0+ | Legacy build system | `meson setup builddir` |
| **Make** | Any | Traditional builds | `make` |

### Build Acceleration

| Tool | Purpose | Speed Improvement | Configuration |
|------|---------|-------------------|---------------|
| **ccache** | Compilation cache | 50-80% faster rebuilds | Enabled by default |
| **Ninja** | Parallel builds | 2-4x faster than make | `-G Ninja` |
| **ThinLTO** | Link optimization | 30-50% faster linking | `-DUSE_LTO=ON` |

---

## 🔍 Static Analysis Tools

### Comprehensive Analysis

| Tool | Focus Area | Checks | Configuration |
|------|------------|--------|---------------|
| **clang-tidy** | All-purpose linter | 300+ checks | `.clang-tidy` |
| **cppcheck** | Bug detection | Security, memory, UB | `ninja cppcheck` |
| **IWYU** | Include optimization | Header usage | `ninja iwyu` |

### clang-tidy Checks

**Security:** `cert-*`, `clang-analyzer-security-*`
- Buffer overflows
- Null pointer dereferences
- Use-after-free
- Integer overflows
- Format string vulnerabilities

**Bugs:** `bugprone-*`
- Logic errors
- Copy-paste errors
- Suspicious constructs
- Undefined behavior

**Performance:** `performance-*`
- Inefficient algorithms
- Unnecessary copies
- Move semantics opportunities

**Readability:** `readability-*`
- Naming conventions
- Code clarity
- Function complexity
- Magic numbers

**Concurrency:** `concurrency-*`
- Race conditions
- Deadlocks
- Thread safety

### Usage Examples

```bash
# Enable during build
cmake -B build -G Ninja -DENABLE_CLANG_TIDY=ON
ninja -C build

# Manual analysis
ninja -C build clang-tidy

# Run all static analysis
cmake -B build -G Ninja -DENABLE_STATIC_ANALYSIS=ON
ninja -C build static-analysis

# Individual tools
ninja -C build cppcheck
ninja -C build cppcheck-text
ninja -C build iwyu
```

---

## 📊 Code Coverage Tools

### LLVM Coverage (Clang)

**Tools:**
- `llvm-profdata`: Merge profile data
- `llvm-cov`: Generate coverage reports

**Workflow:**
```bash
# 1. Build with coverage
cmake -B build -G Ninja -DENABLE_COVERAGE=ON
ninja -C build

# 2. Run tests
ninja -C build test

# 3. Generate report
ninja -C build coverage

# 4. View HTML report
firefox build/coverage/html/index.html
```

**Targets:**
- `coverage-clean`: Clean coverage data
- `coverage-merge`: Merge .profraw files
- `coverage-report`: Text summary
- `coverage-html`: HTML report
- `coverage`: Full analysis

### GCC Coverage (GCC Toolchain)

**Tools:**
- `gcov`: Coverage analysis
- `lcov`: Coverage data processing
- `genhtml`: HTML report generation

**Same workflow as LLVM, automatically detected**

### Coverage Metrics

- **Line Coverage**: % of lines executed
- **Function Coverage**: % of functions called
- **Branch Coverage**: % of branches taken
- **Region Coverage**: % of regions executed (LLVM)

---

## 🧪 Testing Tools

### Test Frameworks

| Tool | Language | Purpose | Usage |
|------|----------|---------|-------|
| **pytest** | Python | Unit/integration tests | `pytest tests/` |
| **CTest** | C/C++ | CMake test runner | `ctest --output-on-failure` |
| **BATS** | Bash | Shell script testing | `bats tests/*.bats` |

### Test Execution

```bash
# Run all Python tests
pytest tests/ -v

# Run with coverage
pytest tests/ --cov=. --cov-report=html

# Parallel execution
pytest tests/ -n auto

# Run CMake tests
ninja -C build test
ctest --test-dir build --output-on-failure

# Run specific test
pytest tests/test_beatty_cycle.py -v
```

---

## 🐛 Debugging Tools

### Debuggers

| Tool | Purpose | Usage |
|------|---------|-------|
| **GDB** | Interactive debugging | `gdb ./build/kernel` |
| **LLDB** | LLVM debugger | `lldb ./build/kernel` |
| **GDB Multiarch** | Cross-arch debugging | `gdb-multiarch` |

### Dynamic Analysis

| Tool | Purpose | Overhead | Usage |
|------|---------|----------|-------|
| **AddressSanitizer** | Memory errors | 2x | `-DENABLE_ASAN=ON` |
| **UBSanitizer** | Undefined behavior | 1.2x | `-DENABLE_UBSAN=ON` |
| **ThreadSanitizer** | Race conditions | 5-15x | `-DENABLE_TSAN=ON` |
| **MemorySanitizer** | Uninitialized reads | 3x | `-DENABLE_MSAN=ON` |

### Profiling Tools

| Tool | Purpose | Usage |
|------|---------|-------|
| **Valgrind** | Memory profiling | `valgrind --leak-check=full ./program` |
| **perf** | CPU profiling | `perf record -g ./program` |
| **strace** | System call tracing | `strace -f ./program` |
| **ltrace** | Library call tracing | `ltrace ./program` |

---

## 🎨 Code Formatting

### Formatters

| Tool | Language | Style | Configuration |
|------|----------|-------|---------------|
| **clang-format** | C/C++ | LLVM-based | `.clang-format` |
| **black** | Python | PEP 8 | Default |
| **cmake-format** | CMake | Custom | Optional |

### Usage

```bash
# Format C/C++ code
clang-format -i path/to/file.c

# Format all C/C++ files
find . -name "*.c" -o -name "*.h" | xargs clang-format -i

# Format Python code
black path/to/file.py

# Format all Python files
black .

# Format CMake files
cmake-format -i CMakeLists.txt
```

---

## 🔒 Security Tools

### Static Security Analysis

| Tool | Focus | Configuration |
|------|-------|---------------|
| **clang-tidy (cert-*)** | CERT secure coding | Enabled in `.clang-tidy` |
| **CodeQL** | Security vulnerabilities | `.github/workflows/codeql.yml` |
| **cppcheck** | Security issues | `--enable=warning` |

### Dynamic Security Analysis

| Tool | Purpose | Usage |
|------|---------|-------|
| **AddressSanitizer** | Memory safety | `-DENABLE_ASAN=ON` |
| **UBSanitizer** | Undefined behavior | `-DENABLE_UBSAN=ON` |

### Dependency Security

| Tool | Purpose | Configuration |
|------|---------|---------------|
| **Dependabot** | Dependency updates | `.github/dependabot.yml` |
| **CodeQL** | Vulnerability scanning | GitHub Actions |

---

## 🐳 Container Tools

### Docker

**Build Container:** `Dockerfile`
- Ubuntu 24.04 base
- LLVM 18 toolchain
- All development tools
- Python dependencies

**Dev Container:** `.devcontainer/Dockerfile`
- Enhanced with VS Code integration
- ccache pre-configured
- User-friendly setup

### Usage

```bash
# Build production container
docker build -t feuerbird-builder -f Dockerfile .

# Build dev container
docker build -t feuerbird-dev -f .devcontainer/Dockerfile .

# Run container
docker run -it -v $(pwd):/workspace feuerbird-dev

# Use with Docker Compose
docker-compose up
```

### Dev Container (VS Code)

**Features:**
- Automatic environment setup
- Pre-installed extensions
- Persistent volumes (ccache)
- Integrated debugging
- Terminal integration

**Usage:**
1. Install "Dev Containers" extension
2. Open project in VS Code
3. `F1` → "Reopen in Container"

---

## 🤖 CI/CD Tools

### GitHub Actions

**Workflows:**
1. **feuerbird_ci.yml**: Main CI pipeline
2. **codeql.yml**: Security scanning
3. **container_ci.yml**: Container builds

### CI Pipeline Stages

**Main CI (feuerbird_ci.yml):**
1. Pre-commit checks (linting, formatting)
2. Matrix builds (4 configurations)
3. Build validation
4. Unit tests (pytest)
5. QEMU smoke tests
6. Architecture matrix (x86_64, aarch64)
7. Final validation

**CodeQL (codeql.yml):**
1. Language detection (C++, Python)
2. Code scanning
3. Security vulnerability detection
4. Scheduled weekly scans

### Local CI Testing

```bash
# Run pre-commit checks
pre-commit run --all-files

# Simulate CI build
cmake -B build -G Ninja -DCMAKE_BUILD_TYPE=RelWithDebInfo
ninja -C build
pytest tests/
```

---

## 📦 Package Management

### Python Dependencies

**File:** `docker-requirements.txt`

**Tools:**
- pytest (testing)
- black (formatting)
- flake8 (linting)
- mypy (type checking)
- sphinx (documentation)

**Install:**
```bash
pip install -r docker-requirements.txt
```

### System Packages

**Ubuntu/Debian:**
```bash
sudo apt-get install \
  clang-18 lld-18 cmake ninja-build \
  cppcheck include-what-you-use \
  lcov gcovr ccache \
  qemu-system-x86 gdb valgrind
```

---

## 📝 Documentation Tools

### Documentation Generators

| Tool | Purpose | Usage |
|------|---------|-------|
| **Doxygen** | C/C++ API docs | `doxygen Doxyfile` |
| **Sphinx** | Python docs | `sphinx-build` |
| **Markdown** | General docs | Any MD viewer |

### Documentation Files

- `README.md`: Project overview
- `docs/BUILD_SYSTEM_GUIDE.md`: Build system guide
- `docs/TECHNICAL_DEBT_ANALYSIS.md`: Gap analysis
- `docs/ARCHITECTURAL_OVERVIEW.md`: Architecture
- `docs/CAPABILITY_MODEL.md`: Security model

---

## 🎯 Tool Selection Decision Matrix

### When to Use Each Tool

| Scenario | Tool | Why |
|----------|------|-----|
| First-time build | Dev Container | Complete environment |
| Daily development | ccache + Ninja | Fast rebuilds |
| Code review | clang-tidy | Comprehensive checks |
| Bug hunting | ASAN + UBSAN | Memory safety |
| Performance issues | Valgrind + perf | Profiling |
| Test coverage | llvm-cov | Coverage analysis |
| Security audit | CodeQL + clang-tidy | Vulnerability detection |
| CI/CD | GitHub Actions | Automated testing |

---

## 🚀 Quick Start Cheat Sheet

### Essential Commands

```bash
# Setup
cmake -B build -G Ninja -DCMAKE_BUILD_TYPE=Debug

# Build
ninja -C build

# Test
pytest tests/
ninja -C build test

# Analyze
ninja -C build static-analysis

# Coverage
ninja -C build coverage

# Clean
ninja -C build clean
ninja -C build ccache-clean

# Info
ninja -C build ccache-info
ninja -C build analysis-summary
```

---

## 📚 Additional Resources

- **CMake Documentation**: https://cmake.org/documentation/
- **LLVM Tools**: https://llvm.org/docs/
- **clang-tidy Checks**: https://clang.llvm.org/extra/clang-tidy/checks/
- **CodeQL**: https://codeql.github.com/docs/
- **Dev Containers**: https://containers.dev/

---

**Last Updated:** 2026-01-03  
**Tooling Version:** 1.0.0

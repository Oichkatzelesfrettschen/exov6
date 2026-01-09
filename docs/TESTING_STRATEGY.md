# Testing Strategy Guide

## Overview

FeuerBird employs a **comprehensive multi-level testing strategy** combining unit tests, integration tests, POSIX compliance tests, and hardware validation:

- **Unit Tests**: C17 custom framework + pytest for rapid validation
- **Integration Tests**: CMake CTest for cross-component verification
- **POSIX Tests**: Automated POSIX 2024 compliance checking
- **Kernel Tests**: QEMU-based boot validation with serial output parsing
- **Coverage**: LLVM code coverage with 40% minimum threshold
- **Continuous Integration**: GitHub Actions enforces test passage on every commit

This strategy ensures **reliability, correctness, and performance** across all layers.

---

## Test Framework Overview

### C17 Custom Testing Framework

**Location**: `tests/framework/`

A lightweight C17 testing framework designed for kernel and system code:

```c
/* Simple test definition */
TEST(my_module, test_addition) {
    ASSERT_EQ(2 + 2, 4);
}

TEST(my_module, test_strings) {
    ASSERT_STR_EQ("hello", "hello");
}

TEST(my_module, test_malloc) {
    int *p = malloc(sizeof(int));
    ASSERT_NOT_NULL(p);
    free(p);
}
```

**Features**:
- Zero runtime overhead
- Compile-time test registration
- Minimal dependencies (no external libraries)
- Support for assertions: EQ, NE, LT, GT, NULL, NOT_NULL, STR_EQ, STR_NE
- Fixtures for setup/teardown
- Test suites for organization

**Running C17 tests**:

```bash
# Build tests
ninja -C build test_runner

# Run all tests
./build/test_runner

# Run specific suite
./build/test_runner --suite memory

# Verbose output
./build/test_runner --verbose

# Stop on first failure
./build/test_runner --fail-fast
```

### Python Testing (pytest)

**Location**: `tests/`

Python tests for build system, scripts, and integration points:

```python
# tests/test_build.py
import subprocess

def test_kernel_builds():
    """Verify kernel compiles without errors"""
    result = subprocess.run(
        ["ninja", "-C", "build", "kernel"],
        capture_output=True
    )
    assert result.returncode == 0, "Kernel build failed"

def test_kernel_binary_valid():
    """Verify kernel ELF format"""
    result = subprocess.run(
        ["file", "build/kernel/kernel"],
        capture_output=True,
        text=True
    )
    assert "ELF 64-bit" in result.stdout
```

**Running Python tests**:

```bash
# Install pytest
pip install pytest

# Run all tests
pytest tests/ -v

# Run specific file
pytest tests/test_build.py -v

# Run specific test
pytest tests/test_build.py::test_kernel_builds -v

# Show print statements
pytest tests/ -s

# Parallel execution
pytest tests/ -n auto
```

### CMake CTest Integration

**Location**: `CMakeLists.txt`

CTest integrates unit tests with CMake build system:

```cmake
# Register test
add_test(NAME test_memory
         COMMAND test_runner --suite memory)

# Set test properties
set_tests_properties(test_memory
    PROPERTIES
    TIMEOUT 30
    LABELS "unit;memory"
)
```

**Running CTest**:

```bash
# Run all tests
ctest --output-on-failure

# Run with timeout per test
ctest --output-on-failure --timeout 30

# Repeat until pass
ctest --repeat until-pass:3

# Run specific test
ctest --output-on-failure -R test_memory

# Verbose output
ctest --output-on-failure -VV

# Run with parallelism
ctest --output-on-failure -j 8
```

---

## Test Categories

### Unit Tests

**Purpose**: Test individual components in isolation

**Examples**:
- Capability table operations (cap_table.c tests)
- Lambda capability creation/use (lambda_cap.c tests)
- Spinlock functionality (spinlock tests)
- Memory allocation (kalloc/kfree tests)

**Location**: `tests/unit/`

**Running**:

```bash
ctest -R unit --output-on-failure
```

### Integration Tests

**Purpose**: Test interactions between components

**Examples**:
- Capability table + capability authentication
- Lambda capabilities with pi-calculus channels
- Zone isolation with cross-zone access checks
- IPC message passing between processes

**Location**: `tests/integration/`

**Running**:

```bash
ctest -R integration --output-on-failure
```

### POSIX Compliance Tests

**Purpose**: Verify POSIX 2024 API compatibility

**Examples**:
- File I/O (open, read, write, close)
- Process management (fork, exec, exit)
- Signal handling
- Memory management (mmap, munmap)

**Location**: `tests/posix/`

**Status**: DISABLED (requires full syscall layer)

**Running** (when enabled):

```bash
ctest -R posix --output-on-failure
```

### Personality Tests

**Purpose**: Test OS personality compatibility

**Examples**:
- **BSD personality**: BSD syscalls, semantics
- **Illumos personality**: OpenSolaris/Illumos compatibility
- **Linux personality**: Linux syscall compatibility

**Location**: `tests/personality/`

**Running**:

```bash
# Linux personality (available everywhere)
ctest -R personality_linux --output-on-failure

# BSD personality (requires BSD headers)
ctest -R personality_bsd --output-on-failure

# Illumos personality (requires Illumos/Solaris)
ctest -R personality_illumos --output-on-failure
```

### Kernel Boot Tests

**Purpose**: Validate kernel initialization and boot sequence

**Examples**:
- Kernel compiles and links
- ELF format validation
- Multiboot2 header present
- Serial output contains success marker
- QEMU boot succeeds

**Location**: `tests/boot/`

**Running**:

```bash
# Build-time validation
ninja -C build kernel

# Boot in QEMU
./scripts/run_qemu.sh

# Check boot output
timeout 30s qemu-system-x86_64 -kernel build/kernel/kernel \
  -nographic -no-reboot > qemu.log 2>&1
grep "KERNEL_BOOT_SUCCESS" qemu.log
```

### Microbenchmarks

**Purpose**: Measure performance and detect regressions

**Examples**:
- Capability table lookup latency
- Lambda capability execution time
- IPC round-trip time
- Spinlock contention

**Location**: `tests/microbench/`

**Running**:

```bash
# Run all benchmarks
ninja -C build benchmark

# Specific benchmark
./build/tests/microbench/benchmark_cap_table

# Compare to baseline
./scripts/compare_benchmarks.sh baseline_metrics.json
```

---

## Adding New Tests

### Adding a C Unit Test

**1. Create test file** (`tests/unit/test_myfeature.c`):

```c
#include "test_framework.h"
#include "myfeature.h"

TEST(myfeature, test_basic_operation) {
    int result = myfeature_init();
    ASSERT_EQ(result, 0);
}

TEST(myfeature, test_error_handling) {
    int result = myfeature_invalid_input(NULL);
    ASSERT_NE(result, 0);  // Should fail
}

SUITE(myfeature, {
    RUN_TEST(test_basic_operation);
    RUN_TEST(test_error_handling);
})
```

**2. Register in CMakeLists.txt**:

```cmake
# tests/CMakeLists.txt
target_sources(test_runner PRIVATE
    unit/test_myfeature.c
)
```

**3. Build and run**:

```bash
ninja -C build test_runner
ctest -R myfeature --output-on-failure
```

### Adding a Python Test

**1. Create test file** (`tests/test_myfeature.py`):

```python
import subprocess
import pytest

@pytest.fixture
def kernel_binary():
    """Ensure kernel is built"""
    result = subprocess.run(
        ["ninja", "-C", "build", "kernel"],
        capture_output=True
    )
    if result.returncode != 0:
        pytest.skip("Kernel build failed")
    return "build/kernel/kernel"

def test_myfeature_works(kernel_binary):
    """Test my feature"""
    result = subprocess.run(
        [kernel_binary, "--test"],
        capture_output=True
    )
    assert result.returncode == 0

@pytest.mark.slow
def test_myfeature_stress():
    """Stress test my feature"""
    for i in range(1000):
        assert myfeature_operation(i) == expected_result(i)
```

**2. Run with pytest**:

```bash
pytest tests/test_myfeature.py -v

# Mark slow tests and skip them
pytest tests/ -v -m "not slow"
```

---

## Code Coverage

### Enabling Coverage

**1. Install LLVM coverage tools**:

```bash
# Ubuntu/Debian
sudo apt install llvm

# macOS
brew install llvm

# Arch
sudo pacman -S llvm
```

**2. Configure CMake with coverage**:

```bash
conan install . -pr:h profiles/debug.profile
cmake -S . -B build -G Ninja \
  -DCMAKE_TOOLCHAIN_FILE=build/generators/conan_toolchain.cmake \
  -DCMAKE_BUILD_TYPE=Debug \
  -DENABLE_COVERAGE=ON
```

**3. Build and run tests**:

```bash
ninja -C build
ctest --output-on-failure
```

### Generating Coverage Report

```bash
# Generate coverage report
ninja -C build coverage-llvm

# View report
llvm-cov report build/kernel/kernel \
  -instr-profile=build/default.profdata

# HTML report
llvm-cov show build/kernel/kernel \
  -instr-profile=build/default.profdata \
  -output-dir=coverage_html \
  -format=html
```

### Coverage Thresholds

**Minimum coverage**: 40% of code

```bash
# Check coverage percentage
COVERAGE=$(llvm-cov report build/kernel/kernel \
  -instr-profile=build/default.profdata \
  | grep TOTAL | awk '{print $NF}' | sed 's/%//')

if (( $(echo "$COVERAGE < 40" | bc -l) )); then
    echo "Coverage $COVERAGE% below 40% threshold"
    exit 1
fi
```

---

## Running Tests Locally

### Quick Test Run (5-10 minutes)

```bash
# Build
ninja -C build

# Run fast tests only
pytest tests/ -v -m "not slow" --timeout=10
ctest -R "unit|integration" --output-on-failure --timeout 30
```

### Full Test Suite (30-60 minutes)

```bash
# Clean build
rm -rf build

# Configure
cmake -S . -B build -G Ninja \
  -DCMAKE_TOOLCHAIN_FILE=build/generators/conan_toolchain.cmake \
  -DCMAKE_BUILD_TYPE=Debug

# Build with all features
ninja -C build

# Run all tests
pytest tests/ -v
ctest --output-on-failure

# Generate coverage
ninja -C build coverage-llvm
llvm-cov report build/kernel/kernel -instr-profile=build/default.profdata

# Boot test
./scripts/run_qemu.sh
```

### Release Build Testing (60-90 minutes)

```bash
# Clean build with release profile
rm -rf build
conan install . -pr:h profiles/release.profile -pr:b profiles/release.profile

cmake -S . -B build -G Ninja \
  -DCMAKE_TOOLCHAIN_FILE=build/generators/conan_toolchain.cmake \
  -DCMAKE_BUILD_TYPE=Release

# Build with LTO/PGO
ninja -C build

# Run benchmarks
ninja -C build benchmark
./build/tests/microbench/benchmark_*

# Boot test
qemu-system-x86_64 -kernel build/kernel/kernel -nographic
```

---

## Continuous Integration

### GitHub Actions Workflow

**File**: `.github/workflows/feuerbird_ci.yml`

Tests automatically run on every push and pull request:

```yaml
name: FeuerBird CI

on: [push, pull_request]

jobs:
  test:
    runs-on: ubuntu-latest
    strategy:
      matrix:
        build_type: [Debug, Release]
        compiler: [clang, gcc]
    steps:
      - uses: actions/checkout@v4

      - name: Install dependencies
        run: |
          sudo apt update
          sudo apt install -y llvm clang gcc ninja-build

      - name: Install Conan
        run: pip install conan

      - name: Configure
        run: |
          conan install . -pr:h profiles/default.profile
          cmake -S . -B build -G Ninja \
            -DCMAKE_TOOLCHAIN_FILE=build/generators/conan_toolchain.cmake \
            -DCMAKE_BUILD_TYPE=${{ matrix.build_type }}

      - name: Build
        run: ninja -C build

      - name: Run tests
        run: ctest --output-on-failure --repeat until-pass:2

      - name: Generate coverage
        if: matrix.build_type == 'Debug'
        run: |
          ninja -C build coverage-llvm
          llvm-cov report build/kernel/kernel \
            -instr-profile=build/default.profdata

      - name: Upload coverage
        if: matrix.build_type == 'Debug'
        uses: codecov/codecov-action@v3
        with:
          files: ./build/coverage.info
```

**Build Matrix**:
- **Compilers**: Clang, GCC
- **Build types**: Debug, Release
- **Coverage**: Collected and uploaded to codecov

---

## Debugging Failed Tests

### Enable Verbose Output

```bash
# C test framework
./build/test_runner --verbose

# CTest
ctest --output-on-failure -VV

# pytest
pytest tests/ -v -s  # -s shows print statements
```

### Debug with GDB

```bash
# Run test under debugger
gdb --args ./build/test_runner --suite memory

# Breakpoint on test failure
(gdb) break assertion_fail
(gdb) run
```

### Address Sanitizer

```bash
# Build with ASAN
conan install . -pr:h profiles/debug.profile
cmake -S . -B build -G Ninja \
  -DCMAKE_TOOLCHAIN_FILE=build/generators/conan_toolchain.cmake \
  -DCMAKE_BUILD_TYPE=Debug \
  -DENABLE_ASAN=ON

ninja -C build
ctest --output-on-failure
# ASAN reports memory errors with backtraces
```

### Undefined Behavior Sanitizer

```bash
# Build with UBSAN
conan install . -pr:h profiles/debug.profile
cmake -S . -B build -G Ninja \
  -DCMAKE_TOOLCHAIN_FILE=build/generators/conan_toolchain.cmake \
  -DCMAKE_BUILD_TYPE=Debug \
  -DENABLE_UBSAN=ON

ninja -C build
ctest --output-on-failure
# UBSAN reports undefined behavior with backtraces
```

---

## Performance Benchmarking

### Baseline Metrics

**File**: `tests/microbench/baseline_metrics.json`

Records baseline performance for regression detection:

```json
{
  "cap_table_lookup": {
    "mean_cycles": 42.3,
    "std_dev": 1.2,
    "date": "2025-01-09"
  },
  "lambda_cap_use": {
    "mean_cycles": 156.8,
    "std_dev": 3.4,
    "date": "2025-01-09"
  },
  "ipc_roundtrip": {
    "mean_cycles": 892.1,
    "std_dev": 15.6,
    "date": "2025-01-09"
  }
}
```

### Running Benchmarks

```bash
# Run all benchmarks
ninja -C build benchmark

# Specific benchmark
./build/tests/microbench/benchmark_cap_table

# With performance counters
perf stat ./build/tests/microbench/benchmark_cap_table

# Compare to baseline (>10% regression fails)
./scripts/compare_benchmarks.sh baseline_metrics.json
```

### Microbenchmark Template

**File**: `tests/microbench/benchmark_myfeature.c`

```c
#include "benchmark.h"
#include "myfeature.h"

void benchmark_myfeature_basic(void) {
    /* Setup */
    myfeature_t *feat = myfeature_create();

    /* Warmup */
    for (int i = 0; i < 100; i++) {
        myfeature_operation(feat);
    }

    /* Benchmark */
    uint64_t start = rdtsc();
    for (int i = 0; i < 100000; i++) {
        myfeature_operation(feat);
    }
    uint64_t end = rdtsc();

    /* Report */
    double cycles_per_op = (double)(end - start) / 100000;
    printf("myfeature_operation: %.1f cycles\n", cycles_per_op);

    myfeature_free(feat);
}
```

---

## Troubleshooting

### Test Compilation Fails

**Problem**: Undefined symbols during test linking

```
undefined reference to `kernel_function'
```

**Solution**: Ensure kernel source files are compiled

```cmake
# In CMakeLists.txt
target_link_libraries(test_runner PRIVATE
    kernel_core_stubs  # or other kernel library targets
)
```

### Test Timeout

**Problem**: Test hangs indefinitely

```
Test timeout after 30 seconds
```

**Solution**: Increase timeout or fix hanging code

```bash
# Increase timeout
set_tests_properties(test_name PROPERTIES TIMEOUT 60)

# Debug with strace
strace -e trace=all ./build/test_runner
```

### Coverage Too Low

**Problem**: Coverage below 40% threshold

```
Coverage 32% below 40% threshold
```

**Solution**: Add tests for uncovered code

```bash
# Find uncovered lines
llvm-cov show build/kernel/kernel \
  -instr-profile=build/default.profdata \
  -use-color

# Add tests targeting uncovered branches
```

---

## Best Practices

### 1. Test Early and Often

```bash
# After every significant change
ninja -C build && ctest --output-on-failure
```

### 2. Write Tests for Bugs

When fixing a bug, write a test that catches it:

```c
TEST(myfeature, test_regression_issue_123) {
    // This test would have caught the bug fixed in PR #123
    int result = myfeature_edge_case();
    ASSERT_EQ(result, EXPECTED_VALUE);
}
```

### 3. Use Fixtures for Setup/Teardown

```c
void setup_memory_test(void) {
    memory_test_heap = kalloc();
}

void teardown_memory_test(void) {
    kfree(memory_test_heap);
}

TEST(memory, test_allocation, setup_memory_test, teardown_memory_test) {
    ASSERT_NOT_NULL(memory_test_heap);
}
```

### 4. Separate Unit and Integration Tests

```bash
# Fast unit tests (< 1 second each)
ctest -R unit --output-on-failure

# Slower integration tests (< 10 seconds each)
ctest -R integration --output-on-failure
```

### 5. Mark Slow Tests

```python
@pytest.mark.slow
def test_stress_load(self):
    """Takes 5 minutes to run"""
    for i in range(1000000):
        do_work()
```

```bash
# Skip slow tests in CI
pytest tests/ -m "not slow"
```

---

## See Also

- `tests/` - Test source code directory
- `CMakeLists.txt` - Test configuration
- `.github/workflows/feuerbird_ci.yml` - CI/CD configuration
- `docs/ARCHITECTURE.md` - System architecture for understanding what to test

# Modern LLVM Build System Guide

This document describes the modernized CMake/Ninja/Clang/LLVM build system for the FeuerBird exokernel project, including Link Time Optimization (LTO), LLVM LLD linker, and Polly polyhedral optimizations.

## Overview

The build system has been enhanced to provide a complete modern LLVM toolchain experience:

- **CMake 3.16+** with Ninja generator for fast parallel builds
- **Clang 18** as the primary C/C++ compiler with C23 standard support  
- **LLVM LLD** linker for faster linking and better optimization
- **LLVM ThinLTO** for interprocedural optimization across translation units
- **LLVM Polly** for polyhedral loop optimizations
- **LLVM Sanitizers** for runtime error detection
- **Modern toolchain** using llvm-ar, llvm-objcopy, and other LLVM tools

## Build System Options

### CMake Options

The following CMake options are available to configure the build:

| Option | Default | Description |
|--------|---------|-------------|
| `USE_LLD` | OFF | Use LLVM LLD linker instead of system default |
| `USE_LTO` | OFF | Enable LLVM ThinLTO interprocedural optimization |
| `USE_POLLY` | OFF | Enable LLVM Polly polyhedral optimizations |
| `ENABLE_ASAN` | OFF | Enable AddressSanitizer for memory error detection |
| `ENABLE_TSAN` | OFF | Enable ThreadSanitizer for data race detection |
| `ENABLE_UBSAN` | OFF | Enable UndefinedBehaviorSanitizer |
| `USE_TICKET_LOCK` | OFF | Use ticket-based spinlocks |
| `IPC_DEBUG` | OFF | Enable IPC debug logging |
| `USE_CAPNP` | OFF | Build Cap'n Proto support |
| `USE_SIMD` | OFF | Enable SIMD math routines |

### Meson Options

The equivalent options for Meson builds:

| Option | Default | Description |
|--------|---------|-------------|
| `use_lld` | false | Use LLVM LLD linker |
| `use_lto` | false | Enable LLVM ThinLTO |
| `use_polly` | false | Enable LLVM Polly optimizations |
| `enable_asan` | false | Enable AddressSanitizer |
| `enable_tsan` | false | Enable ThreadSanitizer |
| `enable_ubsan` | false | Enable UndefinedBehaviorSanitizer |

## Quick Start

### Prerequisites

Install the modern LLVM toolchain:

```bash
# Ubuntu/Debian
sudo apt-get install -y \
    clang-18 \
    lld-18 \
    llvm-18 \
    llvm-18-dev \
    llvm-18-tools \
    ninja-build \
    cmake

# Python tools
pip3 install --user meson ninja pytest
```

### CMake Builds

#### Basic build
```bash
cmake -S . -B build -G Ninja
ninja -C build
```

#### Optimized build with modern LLVM features
```bash
cmake -S . -B build -G Ninja \
    -DUSE_LLD=ON \
    -DUSE_LTO=ON \
    -DUSE_POLLY=ON
ninja -C build
```

#### Debug build with sanitizers
```bash
cmake -S . -B build-debug -G Ninja \
    -DCMAKE_BUILD_TYPE=Debug \
    -DENABLE_ASAN=ON \
    -DENABLE_UBSAN=ON
ninja -C build-debug
```

### Meson Builds

#### Basic build
```bash
CC=clang CXX=clang++ meson setup build
ninja -C build
```

#### Optimized build with modern LLVM features
```bash
CC=clang CXX=clang++ meson setup build \
    -Duse_lld=true \
    -Duse_lto=true \
    -Duse_polly=true
ninja -C build
```

## Advanced Features

### Link Time Optimization (LTO)

LLVM ThinLTO provides interprocedural optimization across the entire program:

- **Faster than traditional LTO**: Parallelized optimization
- **Better optimization**: Cross-module inlining and analysis
- **Incremental**: Only reoptimizes changed modules

Example performance improvements:
- Code size reduction: 10-20%
- Runtime performance: 5-15% improvement
- Link time: Comparable to non-LTO with parallelization

### LLVM LLD Linker

The LLVM LLD linker offers significant advantages:

- **Speed**: 2-5x faster than GNU ld
- **Memory usage**: Lower memory consumption for large projects
- **LLVM integration**: Better optimization integration with Clang
- **Cross-platform**: Consistent behavior across platforms

### Polly Polyhedral Optimization

LLVM Polly performs advanced loop transformations:

- **Loop vectorization**: Automatic SIMD code generation
- **Loop parallelization**: Multi-core optimization
- **Cache optimization**: Memory access pattern optimization
- **Loop tiling**: Improved cache locality

Best for computational kernels and numerical code.

### Sanitizers

Runtime error detection tools:

#### AddressSanitizer (ASan)
- Detects buffer overflows, use-after-free, double-free
- ~2x slowdown, significant memory overhead
- Essential for memory safety validation

#### ThreadSanitizer (TSan)  
- Detects data races and threading bugs
- ~2-20x slowdown depending on thread contention
- Critical for concurrent code validation

#### UndefinedBehaviorSanitizer (UBSan)
- Detects undefined behavior per C standard
- Minimal performance impact
- Catches subtle portability issues

## Performance Comparison

Typical build time and binary size comparison:

| Configuration | Build Time | Binary Size | Runtime Perf |
|---------------|------------|-------------|--------------|
| Baseline | 1.0x | 1.0x | 1.0x |
| LLD | 0.7x | 1.0x | 1.0x |
| LLD + ThinLTO | 1.2x | 0.85x | 1.1x |
| LLD + ThinLTO + Polly | 1.4x | 0.80x | 1.15x |

*Performance will vary based on codebase characteristics*

## CI/CD Integration

The project includes automated testing of all build configurations:

- **Matrix builds**: Test all combinations of features
- **Artifact comparison**: Validate optimization effects
- **Performance regression**: Track binary size and build times
- **Cross-validation**: Compare CMake vs Meson outputs

See `.github/workflows/modern_build_ci.yml` for implementation details.

## Troubleshooting

### Common Issues

#### Clang not found
```bash
# Install specific version
sudo apt-get install clang-18
# Set as default
sudo update-alternatives --install /usr/bin/clang clang /usr/bin/clang-18 100
```

#### LLD linker not found
```bash
# Install LLD
sudo apt-get install lld-18
# Verify installation
which ld.lld-18
```

#### Polly not available
```bash
# Check if Polly is compiled into Clang
clang -mllvm -help | grep polly
# If not available, install full LLVM development package
sudo apt-get install llvm-18-dev
```

#### ThinLTO issues
- Ensure sufficient RAM (4GB+ recommended)
- Use `-flto=thin` not `-flto` 
- Check that all object files use compatible LTO formats

### Debug Information

For debugging build issues:

```bash
# Verbose CMake configuration
cmake -S . -B build -G Ninja --debug-output

# Verbose Meson configuration  
meson setup build --verbose

# Check compiler flags
ninja -C build -v

# Verify LLVM tools
llvm-config-18 --version
llvm-config-18 --bindir
```

## Contributing

When contributing to the build system:

1. Test both CMake and Meson configurations
2. Verify all build options work in isolation and combination
3. Update documentation for new options
4. Add CI tests for new features
5. Measure performance impact of changes

## References

- [LLVM Project Documentation](https://llvm.org/docs/)
- [Clang User Manual](https://clang.llvm.org/docs/UsersManual.html)
- [LLD Linker](https://lld.llvm.org/)
- [LLVM ThinLTO](https://clang.llvm.org/docs/ThinLTO.html)
- [Polly Optimizations](https://polly.llvm.org/)
- [CMake Documentation](https://cmake.org/documentation/)
- [Meson Build System](https://mesonbuild.com/)
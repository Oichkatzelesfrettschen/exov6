# Build System Documentation

## Overview

Phoenix Exokernel uses a modern CMake build system (CMake 3.25+) following 2025 best practices. The legacy Makefile has been deprecated.

## Quick Start

### Using CMake Presets (Recommended)

```bash
# Configure with default preset
cmake --preset=default

# Build
cmake --build build

# Run tests
ctest --preset=default
```

### Available Presets

- **default**: Standard debug build with all features
- **release**: Optimized release build with LTO
- **debug**: Debug build with sanitizers (ASAN + UBSAN)
- **dev**: Quick development iteration (no tests/demos)
- **ci**: CI build with all checks enabled

### Manual Configuration

```bash
# Create build directory
mkdir build && cd build

# Configure
cmake .. -G Ninja \
  -DCMAKE_BUILD_TYPE=Release \
  -DBUILD_TESTS=ON \
  -DBUILD_DEMOS=ON

# Build
ninja

# Or use parallel make
cmake --build . --parallel
```

## Build Options

### Core Features
- `USE_LTO` - Enable LLVM ThinLTO optimization (default: OFF)
- `USE_LLD` - Use LLVM LLD linker (default: OFF)
- `USE_POLLY` - Enable LLVM Polly optimizations (default: OFF)
- `USE_SIMD` - Enable SIMD instruction support (default: OFF)
- `USE_CAPNP` - Build Cap'n Proto support (default: OFF)

### Debug Features
- `ENABLE_ASAN` - Enable AddressSanitizer (default: OFF)
- `ENABLE_TSAN` - Enable ThreadSanitizer (default: OFF)
- `ENABLE_UBSAN` - Enable UndefinedBehaviorSanitizer (default: OFF)
- `ENABLE_MSAN` - Enable MemorySanitizer (default: OFF)
- `IPC_DEBUG` - Enable IPC debug logging (default: OFF)

### Platform Features
- `MCU` - Build for microcontroller target (default: OFF)
- `USE_TICKET_LOCK` - Use ticket-based spinlocks (default: OFF)
- `ENABLE_AVX2` - Enable AVX2 instructions (default: OFF)
- `ENABLE_AVX512` - Enable AVX512 instructions (default: OFF)
- `ENABLE_NEON` - Enable ARM NEON instructions (default: OFF)

### Security Features
- `ENABLE_CET` - Enable Intel CET (default: ON)
- `ENABLE_PAC` - Enable ARM Pointer Authentication (default: ON)
- `ENABLE_STACK_PROTECTOR` - Enable strong stack protection (default: ON)

### Build Configuration
- `BUILD_DEMOS` - Build demonstration programs (default: ON)
- `BUILD_TESTS` - Build test suite (default: ON)
- `BUILD_TOOLS` - Build development tools (default: ON)
- `BUILD_DOCS` - Build documentation (default: OFF)

## Examples

### Debug Build with Sanitizers

```bash
cmake --preset=debug
cmake --build build
```

### Optimized Release Build

```bash
cmake --preset=release
cmake --build build
```

### Development Build (Fast Iteration)

```bash
cmake --preset=dev
cmake --build build
```

### Custom Configuration

```bash
cmake -B build -G Ninja \
  -DCMAKE_BUILD_TYPE=RelWithDebInfo \
  -DENABLE_ASAN=ON \
  -DUSE_LTO=ON \
  -DBUILD_TESTS=OFF
cmake --build build
```

## IDE Integration

### Visual Studio Code

The build system generates `compile_commands.json` automatically for IntelliSense.

1. Install the CMake Tools extension
2. Open the command palette (Ctrl+Shift+P)
3. Run "CMake: Select a Kit"
4. Select your preferred compiler
5. Run "CMake: Configure"

### CLion

CLion has native CMake support:

1. Open the project directory
2. CLion will detect CMakeLists.txt automatically
3. Select a CMake profile from the dropdown
4. Build using the IDE controls

## Migration from Legacy Makefile

The legacy Makefile has been deprecated. Here's how to migrate:

| Old (Makefile) | New (CMake) |
|----------------|-------------|
| `make` | `cmake --build build` |
| `make clean` | `cmake --build build --target clean` |
| `make test` | `ctest --preset=default` |
| `make all` | `cmake --build build --parallel` |
| `CC=clang make` | `cmake --preset=default` (uses Clang by default) |
| `CFLAGS=-O3 make` | `cmake --preset=release` |

## Troubleshooting

### Clean Build

```bash
rm -rf build
cmake --preset=default
cmake --build build
```

### Verbose Build

```bash
cmake --build build --verbose
```

### Show Configuration

```bash
cmake -B build -G Ninja -LAH
```

### Check CMake Version

```bash
cmake --version  # Should be >= 3.25
```

## Advanced Topics

### Cross-Compilation

Use toolchain files in `cmake/`:

```bash
cmake -B build \
  -DCMAKE_TOOLCHAIN_FILE=cmake/toolchain-aarch64.cmake
```

### Custom Compiler

```bash
cmake -B build \
  -DCMAKE_C_COMPILER=clang-18 \
  -DCMAKE_CXX_COMPILER=clang++-18
```

### Out-of-Tree Build

```bash
mkdir ../exov6-build
cd ../exov6-build
cmake ../exov6 -G Ninja
ninja
```

## CMake Development

### Formatting CMake Files

```bash
# Format all CMake files
find . -name "CMakeLists.txt" -o -name "*.cmake" | \
  xargs cmake-format -i
```

### Linting CMake Files

```bash
# Lint all CMake files
cmake-lint CMakeLists.txt
```

### Configuration File

CMake formatting is configured in `.cmake-format.yaml`.

## Resources

- [CMake Documentation](https://cmake.org/documentation/)
- [CMake Presets](https://cmake.org/cmake/help/latest/manual/cmake-presets.7.html)
- [Modern CMake](https://cliutils.gitlab.io/modern-cmake/)
- [CMake Best Practices](https://github.com/cpp-best-practices/cmake_best_practices)

## Standards Compliance

This build system follows:
- CMake 3.25+ standards
- C23 standard (C2x)
- C++23 standard
- 2025 CMake best practices
- Modern generator expressions
- Proper target-based dependency management

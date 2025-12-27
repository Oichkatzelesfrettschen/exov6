# Build Directory Best Practices for FeuerBird Exokernel

## Overview
Based on research and industry best practices for operating system kernel projects, this document outlines the optimal build directory structure for the FeuerBird ExoKernel project.

## Key Principles

### 1. Out-of-Source Builds (CRITICAL)
- **Always** build outside the source tree
- Source directory remains clean and version-control friendly
- Multiple build configurations can coexist (debug, release, cross-compile)
- Easy cleanup: just delete the build directory

### 2. Hierarchical Build Output Structure

```
build/                      # Root build directory (git-ignored)
├── CMakeCache.txt         # CMake configuration cache
├── CMakeFiles/            # CMake internal files
├── bin/                   # Executable outputs
│   ├── kernel.elf        # Main kernel executable
│   ├── tools/            # Build tools (mkfs, etc.)
│   └── demos/            # Demo programs
├── lib/                   # Static/shared libraries
│   ├── libkernel.a       # Kernel library
│   └── libos.a           # LibOS library
├── obj/                   # Object files (intermediate)
│   ├── kernel/           # Kernel object files
│   ├── libos/            # LibOS object files
│   └── user/             # User program objects
├── fs/                    # Filesystem staging
│   └── bin/              # User programs for fs.img
├── images/                # Final output images
│   ├── feuerbird.img    # Bootable OS image
│   ├── fs.img           # Filesystem image
│   └── bootblock        # Boot sector
└── test/                  # Test executables
    ├── unit/             # Unit tests
    └── integration/      # Integration tests
```

## CMake Configuration

### Output Directory Variables
```cmake
# Set global output directories
set(CMAKE_ARCHIVE_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/lib)
set(CMAKE_LIBRARY_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/lib)
set(CMAKE_RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/bin)

# Object file organization
set(CMAKE_OBJECT_PATH_PREFIX ${CMAKE_BINARY_DIR}/obj/)
```

### Per-Configuration Directories (Multi-Config Generators)
```cmake
foreach(CONFIG ${CMAKE_CONFIGURATION_TYPES})
    string(TOUPPER ${CONFIG} CONFIG_UPPER)
    set(CMAKE_ARCHIVE_OUTPUT_DIRECTORY_${CONFIG_UPPER} ${CMAKE_BINARY_DIR}/${CONFIG}/lib)
    set(CMAKE_LIBRARY_OUTPUT_DIRECTORY_${CONFIG_UPPER} ${CMAKE_BINARY_DIR}/${CONFIG}/lib)
    set(CMAKE_RUNTIME_OUTPUT_DIRECTORY_${CONFIG_UPPER} ${CMAKE_BINARY_DIR}/${CONFIG}/bin)
endforeach()
```

### Enforce Out-of-Source Builds
```cmake
if(CMAKE_SOURCE_DIR STREQUAL CMAKE_BINARY_DIR)
    message(FATAL_ERROR "In-source builds are not allowed. Please create a build directory.")
endif()
```

## Build Workflow

### Standard Build Process
```bash
# Create build directory
mkdir -p build && cd build

# Configure (choose one)
cmake .. -DCMAKE_BUILD_TYPE=Debug    # Debug build
cmake .. -DCMAKE_BUILD_TYPE=Release  # Release build

# Build
cmake --build . -j$(nproc)

# Or use make directly
make -j$(nproc)
```

### Multiple Build Configurations
```bash
# Debug build
mkdir -p build-debug && cd build-debug
cmake .. -DCMAKE_BUILD_TYPE=Debug
make -j$(nproc)

# Release build
mkdir -p build-release && cd build-release
cmake .. -DCMAKE_BUILD_TYPE=Release
make -j$(nproc)

# Cross-compile build
mkdir -p build-arm64 && cd build-arm64
cmake .. -DCMAKE_TOOLCHAIN_FILE=../cmake/arm64.cmake
make -j$(nproc)
```

## Benefits of This Structure

1. **Clean Separation**: Source and build artifacts never mix
2. **Parallel Builds**: Object files organized by component prevent conflicts
3. **Easy Distribution**: All outputs in predictable locations
4. **Fast Rebuilds**: Incremental builds work efficiently with organized objects
5. **Testing Isolation**: Test binaries separate from production code
6. **CI/CD Friendly**: Predictable paths for artifact collection

## Linking Optimization

### Object File Organization
- Group object files by subsystem for better cache locality
- Use thin archives for faster linking
- Enable Link-Time Optimization (LTO) for release builds

### Linker Flags for Efficiency
```cmake
# Enable faster linking
set(CMAKE_EXE_LINKER_FLAGS_RELEASE "-O3 -flto")
set(CMAKE_SHARED_LINKER_FLAGS_RELEASE "-O3 -flto")

# Use gold linker if available (faster than ld)
if(CMAKE_CXX_COMPILER_ID STREQUAL "GNU")
    set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} -fuse-ld=gold")
endif()
```

## Tidiness Rules

1. **Never commit build directories**: Add to `.gitignore`
2. **Clean regularly**: `rm -rf build` is safe and complete
3. **Use consistent naming**: `build-<config>` for multiple configurations
4. **Document build types**: Keep a `BUILD.md` with standard configurations
5. **Automate cleanup**: Add `clean-all` target to remove all build-* directories

## Makefile Integration

For projects using both CMake and Make:
```makefile
# Wrapper targets for CMake
cmake-build:
	mkdir -p build && cd build && cmake .. && make -j$(nproc)

cmake-clean:
	rm -rf build build-*

cmake-debug:
	mkdir -p build-debug && cd build-debug && cmake .. -DCMAKE_BUILD_TYPE=Debug && make -j$(nproc)
```

## Performance Considerations

1. **Use tmpfs for builds**: Mount build directory in RAM for faster compilation
2. **Precompiled headers**: Store in `${CMAKE_BINARY_DIR}/pch/`
3. **Compiler cache**: Use ccache with `${HOME}/.ccache` directory
4. **Parallel jobs**: Default to `nproc` for optimal CPU usage

## Summary

This build directory structure provides:
- Clear organization for complex OS kernel projects
- Optimized paths for linking efficiency
- Clean separation of concerns
- Easy maintenance and cleanup
- Professional-grade build system suitable for production use
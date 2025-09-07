# Build System Analysis and Modernization Strategy

## Current Situation

### 1. Repository Structure Issues
- **Multiple duplicate files**: mkfs.c exists in tools/, user/, and kernel/
- **Header files scattered**: Headers in include/, kernel/, libos/, and subdirectories
- **Missing definitions**: T_DIR, T_FILE not defined in current headers
- **Type conflicts**: System types conflicting with host OS (macOS) types

### 2. Build Problems Identified
- **Host vs Target confusion**: Tools like mkfs.c trying to include kernel headers
- **Missing cross-compilation setup**: Building for host instead of target
- **Include path issues**: Headers not finding dependencies
- **Type redefinitions**: off_t, pthread_attr_t, timeval conflicting with macOS

### 3. Architecture Confusion
- Mixed x86, x86_64, and ARM code
- No clear separation between architectures
- Boot code assumes x86 BIOS boot

## Modernization Strategy

### Phase 1: Immediate Fixes

#### 1.1 Define Missing Constants
Create a unified file types header:
```c
// include/file_types.h
#define T_DIR  1   // Directory
#define T_FILE 2   // File
#define T_DEV  3   // Device
```

#### 1.2 Fix mkfs Tool
Make mkfs.c completely standalone:
- Remove kernel header dependencies
- Use standard C library only
- Define necessary structures locally

#### 1.3 Separate Build Targets
```cmake
# Host tools (native compilation)
add_executable(mkfs_host tools/mkfs_standalone.c)

# Kernel (cross-compilation or freestanding)
add_executable(kernel.elf ${KERNEL_SOURCES})
target_compile_options(kernel.elf PRIVATE -ffreestanding -nostdlib)
```

### Phase 2: Cross-Compilation Setup

#### 2.1 Toolchain Configuration
```cmake
# cmake/Toolchain-x86_64.cmake
set(CMAKE_SYSTEM_NAME Generic)
set(CMAKE_SYSTEM_PROCESSOR x86_64)
set(CMAKE_C_COMPILER x86_64-elf-gcc)
set(CMAKE_ASM_COMPILER x86_64-elf-as)
set(CMAKE_C_FLAGS "-ffreestanding -nostdlib -mcmodel=kernel")
```

#### 2.2 AArch64 Support
```cmake
# cmake/Toolchain-aarch64.cmake
set(CMAKE_SYSTEM_NAME Generic)
set(CMAKE_SYSTEM_PROCESSOR aarch64)
set(CMAKE_C_COMPILER aarch64-elf-gcc)
set(CMAKE_ASM_COMPILER aarch64-elf-as)
```

### Phase 3: Architecture Abstraction

#### 3.1 Directory Structure
```
kernel/
├── arch/
│   ├── x86_64/
│   │   ├── boot.S
│   │   ├── trap.S
│   │   └── mmu.c
│   └── aarch64/
│       ├── boot.S
│       ├── exception.S
│       └── mmu.c
├── core/       # Architecture-independent
└── drivers/    # With arch-specific subdirs
```

#### 3.2 Build System Architecture Selection
```cmake
if(ARCH STREQUAL "x86_64")
    set(ARCH_SOURCES ${X86_64_SOURCES})
elseif(ARCH STREQUAL "aarch64")
    set(ARCH_SOURCES ${AARCH64_SOURCES})
endif()
```

### Phase 4: QEMU Testing Strategy

#### 4.1 x86_64 QEMU
```bash
qemu-system-x86_64 \
    -kernel kernel.elf \
    -drive file=fs.img,format=raw \
    -m 512 \
    -smp 2 \
    -nographic
```

#### 4.2 AArch64 QEMU
```bash
qemu-system-aarch64 \
    -M virt \
    -cpu cortex-a57 \
    -kernel kernel.elf \
    -drive file=fs.img,format=raw \
    -m 512 \
    -nographic
```

## Implementation Priority

1. **Fix mkfs compilation** (standalone tool)
2. **Create minimal bootable x86_64 kernel**
3. **Test in QEMU x86_64**
4. **Add AArch64 boot code**
5. **Test in QEMU AArch64**

## Key Decisions

1. **Use freestanding environment** for kernel (-ffreestanding)
2. **Separate host tools** from kernel build
3. **Start with x86_64** as primary target
4. **Add AArch64** as secondary target
5. **Use QEMU** for all testing (no hardware needed)

## Build Commands

### Quick Start (x86_64)
```bash
# Configure
mkdir build && cd build
cmake .. -DARCH=x86_64 -DCMAKE_BUILD_TYPE=Debug

# Build
cmake --build .

# Run in QEMU
cmake --build . --target qemu
```

### Cross-Compilation
```bash
# Install toolchain first
brew install x86_64-elf-gcc

# Configure with toolchain
cmake .. -DCMAKE_TOOLCHAIN_FILE=../cmake/Toolchain-x86_64.cmake

# Build and test
cmake --build . && cmake --build . --target qemu
```
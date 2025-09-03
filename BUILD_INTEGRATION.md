# Build System Integration for C++23 Migration

## Current Build System Analysis

### Makefile Structure
- **Primary Makefile**: Traditional Unix-style build
- **Architecture Support**: x86_64, i386, aarch64, armv7, powerpc
- **Compiler**: Currently using C17 with cross-compilers
- **Dependencies**: Manual dependency tracking

### Meson Build
- **Configuration**: `meson.build` with C17 standard
- **Options**: Ticket locks, IPC debug, Cap'n Proto support
- **Targets**: Kernel, LibOS, User utilities

## Required Build System Changes

### 1. Compiler Configuration

#### Makefile Updates
```makefile
# C++23 Configuration
CXX_STD := c++23
CXX := clang++

# Include libc++ paths
include use_libcxx.sh
export KERNEL_CXXFLAGS
export LIBOS_CXXFLAGS  
export USER_CXXFLAGS

# Source file extensions
KERNEL_CXX_SRCS := $(wildcard kernel/*.cpp)
LIBOS_CXX_SRCS := $(wildcard libos/*.cpp)
USER_CXX_SRCS := $(wildcard user/*.cpp)

# Object files from C++ sources
KERNEL_CXX_OBJS := $(KERNEL_CXX_SRCS:.cpp=.o)
LIBOS_CXX_OBJS := $(LIBOS_CXX_SRCS:.cpp=.o)
USER_CXX_OBJS := $(USER_CXX_SRCS:.cpp=.o)

# Pattern rules for C++23
kernel/%.o: kernel/%.cpp
	$(CXX) $(KERNEL_CXXFLAGS) -c -o $@ $<

libos/%.o: libos/%.cpp
	$(CXX) $(LIBOS_CXXFLAGS) -c -o $@ $<

user/%.o: user/%.cpp
	$(CXX) $(USER_CXXFLAGS) -c -o $@ $<
```

#### Meson Updates
```meson
# Add C++23 support
project('exov6', ['c', 'cpp'],
  default_options : [
    'c_std=c17',
    'cpp_std=c++23',
    'warning_level=3',
    'werror=true',
    'cpp_eh=none',      # No exceptions
    'cpp_rtti=false',   # No RTTI
  ]
)

# Zone-specific arguments
kernel_cpp_args = [
  '-DKERNEL_BUILD',
  '-ffreestanding',
  '-nostdlib',
]

libos_cpp_args = [
  '-DLIBOS_BUILD',
]

user_cpp_args = [
  '-DUSER_BUILD',
]

# Link against custom libc++
libcxx_dep = declare_dependency(
  include_directories: include_directories('llvm-libc++/include/c++/v1'),
  link_args: ['-L' + meson.source_root() + '/llvm-libc++/lib',
              '-lc++', '-lc++abi', '-lunwind']
)
```

### 2. Dependency Graph

```
llvm-libc++ (Built First)
    ├── libc++.a
    ├── libc++abi.a
    └── libunwind.a
            ↓
    Kernel Zone (Freestanding)
        ├── capability.cpp
        ├── memory.cpp
        ├── ipc.cpp
        └── synchronization.cpp
            ↓
    LibOS Zone (Hosted)
        ├── posix.cpp
        ├── threading.cpp
        ├── signals.cpp
        └── filesystem.cpp
            ↓
    User Zone (Applications)
        ├── shell.cpp
        ├── utilities.cpp
        └── demos.cpp
```

### 3. Module Build Configuration

#### C++23 Module Support
```makefile
# Module interface units
KERNEL_MODULES := \
    kernel/exo.capability.ixx \
    kernel/exo.memory.ixx \
    kernel/exo.ipc.ixx

# Build module interfaces
%.pcm: %.ixx
	$(CXX) $(KERNEL_CXXFLAGS) -std=c++23 --precompile -o $@ $<

# Build module implementations  
%.o: %.pcm
	$(CXX) $(KERNEL_CXXFLAGS) -c -o $@ $<
```

### 4. License-Based Build Separation

#### Directory-Specific Builds
```makefile
# BSD-licensed components (always built)
BSD_DIRS := bsd/kernel bsd/libos bsd/user
BSD_OBJS := $(foreach dir,$(BSD_DIRS),$(wildcard $(dir)/*.o))

# GPL-licensed components (optional)
ifdef BUILD_GPL
GPL_DIRS := gpl/ddekit gpl/rump gpl/drivers
GPL_OBJS := $(foreach dir,$(GPL_DIRS),$(wildcard $(dir)/*.o))
endif

# MIT-licensed components
MIT_DIRS := mit/tools mit/libs
MIT_OBJS := $(foreach dir,$(MIT_DIRS),$(wildcard $(dir)/*.o))

# Limine bootloader (separate build)
limine/limine: limine/Makefile
	$(MAKE) -C limine

# Final linking respects boundaries
kernel: $(BSD_OBJS) $(MIT_OBJS) $(if $(BUILD_GPL),$(GPL_OBJS))
	$(LD) $(LDFLAGS) -o $@ $^
```

### 5. Incremental Migration Support

#### Dual Language Support
```makefile
# Support both C and C++ during migration
KERNEL_SRCS := $(wildcard kernel/*.c) $(wildcard kernel/*.cpp)
KERNEL_OBJS := $(KERNEL_SRCS:.c=.o)
KERNEL_OBJS := $(KERNEL_OBJS:.cpp=.o)

# Language-specific flags
%.o: %.c
	$(CC) $(CFLAGS) -c -o $@ $<

%.o: %.cpp
	$(CXX) $(CXXFLAGS) -c -o $@ $<

# Ensure C++ objects link correctly with C
kernel/main.o: CXXFLAGS += -fno-exceptions -fno-rtti
```

### 6. Build Targets & Dependencies

#### Clean Build Hierarchy
```makefile
.PHONY: all bootstrap kernel libos user clean

all: bootstrap kernel libos user fs.img

bootstrap: llvm-libc++/lib/libc++.a
	@echo "C++23 runtime ready"

llvm-libc++/lib/libc++.a:
	./scripts/bootstrap_libcxx.sh

kernel: bootstrap $(KERNEL_OBJS)
	$(LD) -o kernel.elf $(KERNEL_OBJS) $(KERNEL_LDFLAGS)

libos: kernel $(LIBOS_OBJS)
	$(AR) rcs libos.a $(LIBOS_OBJS)

user: libos $(USER_PROGS)
	@echo "User programs built"

fs.img: user
	./mkfs fs.img $(USER_PROGS)

clean:
	rm -f $(KERNEL_OBJS) $(LIBOS_OBJS) $(USER_OBJS)
	rm -f *.elf *.a fs.img
```

### 7. Testing Integration

#### Test Build Targets
```makefile
# Unit tests with C++23
test/%.test: test/%.cpp
	$(CXX) $(USER_CXXFLAGS) -o $@ $< -lgtest -lgtest_main

# POSIX compliance tests
posix-test: user
	./scripts/run_posix_tests.sh

# Performance benchmarks
benchmark: kernel
	./tools/phoenix_prof

# Static analysis
analyze:
	clang-tidy $(KERNEL_CXX_SRCS) -- $(KERNEL_CXXFLAGS)
```

### 8. CI/CD Configuration

#### GitHub Actions Workflow
```yaml
name: C++23 Build

on: [push, pull_request]

jobs:
  build:
    runs-on: ubuntu-latest
    steps:
    - uses: actions/checkout@v3
    
    - name: Install LLVM 18
      run: |
        wget https://apt.llvm.org/llvm.sh
        chmod +x llvm.sh
        sudo ./llvm.sh 18
    
    - name: Bootstrap libc++
      run: ./scripts/bootstrap_libcxx.sh
    
    - name: Build Kernel
      run: make kernel CXX_STD=c++23
    
    - name: Build LibOS
      run: make libos CXX_STD=c++23
    
    - name: Build User
      run: make user CXX_STD=c++23
    
    - name: Run Tests
      run: make test
```

## Build Performance Optimization

### Parallel Build Support
```makefile
# Optimize for parallel builds
MAKEFLAGS += -j$(shell nproc)

# Use ccache if available
CCACHE := $(shell which ccache)
ifdef CCACHE
CXX := $(CCACHE) $(CXX)
CC := $(CCACHE) $(CC)
endif

# Precompiled headers for common includes
PRECOMPILED_HEADERS := include/common.hpp.gch

include/%.hpp.gch: include/%.hpp
	$(CXX) $(CXXFLAGS) -x c++-header -o $@ $<
```

### Incremental Build Cache
```makefile
# Dependency generation
DEPFLAGS = -MMD -MP -MF $(@:.o=.d)

%.o: %.cpp
	$(CXX) $(DEPFLAGS) $(CXXFLAGS) -c -o $@ $<

# Include generated dependencies
-include $(KERNEL_OBJS:.o=.d)
-include $(LIBOS_OBJS:.o=.d)
-include $(USER_OBJS:.o=.d)
```

## Migration Build Sequence

### Step 1: Prepare Environment
```bash
make clean
./scripts/bootstrap_libcxx.sh
source use_libcxx.sh
```

### Step 2: Restructure Directories  
```bash
./scripts/restructure_by_license.sh
./scripts/deduplicate_utilities.sh
```

### Step 3: Update Build Files
```bash
cp Makefile Makefile.c17.backup
cp Makefile.cpp23 Makefile
meson setup build-cpp23 --wipe
```

### Step 4: Incremental Migration
```bash
# Migrate kernel first
make kernel CXX_STD=c++23

# Then LibOS
make libos CXX_STD=c++23

# Finally user space
make user CXX_STD=c++23
```

### Step 5: Validate
```bash
make test
make posix-test
make benchmark
```

## Troubleshooting

### Common Issues

1. **Link Errors with C/C++ Mix**
   - Solution: Use `extern "C"` for C interfaces
   - Ensure consistent calling conventions

2. **Missing C++23 Features**
   - Solution: Update to LLVM 18+
   - Check feature test macros

3. **Larger Binary Size**
   - Solution: Enable LTO
   - Strip debug symbols for release

4. **Module Build Failures**
   - Solution: Ensure CMake 3.28+
   - Use Ninja instead of Make

## Performance Metrics

### Build Time Targets
- Full rebuild: < 60 seconds
- Incremental: < 5 seconds
- Module rebuild: < 2 seconds

### Binary Size Targets
- Kernel: < 500KB
- LibOS: < 1MB
- Utilities: < 50KB each

### Memory Usage
- Build RAM: < 4GB
- Disk space: < 500MB
- ccache: < 1GB
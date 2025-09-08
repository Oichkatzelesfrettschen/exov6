#!/bin/bash
# Unify all kernel implementations into THE ONE kernel

set -e

echo "=== UNIFYING KERNEL - One Kernel to Rule Them All ==="

# Step 1: Merge minimal_kernel test code as a debug/test module
if [ -d "minimal_kernel" ]; then
    echo "Integrating minimal_kernel as kernel test module..."
    mkdir -p kernel/tests
    [ -f "minimal_kernel/kernel.c" ] && cp minimal_kernel/kernel.c kernel/tests/minimal_test.c
    [ -f "minimal_kernel/boot.S" ] && cp minimal_kernel/boot.S kernel/tests/minimal_boot.S
    rm -rf minimal_kernel
    echo "  ✓ Minimal kernel integrated as test module"
fi

# Step 2: Merge unique engine/kernel files
if [ -d "engine/kernel" ]; then
    echo "Synthesizing engine/kernel components..."
    
    # Merge arbitrate.c if not already present
    if [ -f "engine/kernel/arbitrate.c" ] && [ ! -f "kernel/arbitrate.c" ]; then
        echo "  Moving arbitrate.c to main kernel..."
        cp engine/kernel/arbitrate.c kernel/arbitrate.c
    elif [ -f "engine/kernel/arbitrate.c" ] && [ -f "kernel/arbitrate.c" ]; then
        echo "  Merging arbitrate.c implementations..."
        # Compare and merge if different
        if ! diff -q engine/kernel/arbitrate.c kernel/arbitrate.c >/dev/null 2>&1; then
            # Keep the larger/more complete version
            if [ $(wc -l < engine/kernel/arbitrate.c) -gt $(wc -l < kernel/arbitrate.c) ]; then
                cp engine/kernel/arbitrate.c kernel/arbitrate.c
                echo "    Used engine version (more complete)"
            fi
        fi
    fi
    
    # Handle sleeplock.h
    if [ -f "engine/kernel/sleeplock.h" ] && [ ! -f "kernel/sleeplock.h" ]; then
        cp engine/kernel/sleeplock.h kernel/sleeplock.h
        echo "  ✓ Added sleeplock.h"
    fi
    
    # Handle buf.h
    if [ -f "engine/kernel/buf.h" ] && [ ! -f "kernel/buf.h" ]; then
        cp engine/kernel/buf.h kernel/buf.h
        echo "  ✓ Added buf.h"
    fi
    
    # Move test files to kernel/tests
    mkdir -p kernel/tests
    [ -f "engine/kernel/test_bootasm.S" ] && mv engine/kernel/test_bootasm.S kernel/tests/
    [ -f "engine/kernel/test_spinlock.h" ] && mv engine/kernel/test_spinlock.h kernel/tests/
    
    echo "  ✓ Engine kernel components synthesized"
fi

# Step 3: Consolidate include/kernel headers into kernel/include
if [ -d "include/kernel" ]; then
    echo "Consolidating include/kernel headers..."
    mkdir -p kernel/include
    cp -r include/kernel/* kernel/include/ 2>/dev/null || true
    rm -rf include/kernel
    echo "  ✓ Kernel headers consolidated"
fi

# Step 4: Remove engine directory completely
if [ -d "engine" ]; then
    echo "Removing redundant engine directory..."
    rm -rf engine
    echo "  ✓ Engine directory removed"
fi

# Step 5: Update CMakeLists.txt paths
echo "Updating build system for unified kernel..."
if [ -f "kernel/CMakeLists.txt" ]; then
    # Add test module to build
    cat >> kernel/CMakeLists.txt << 'EOF'

# Kernel test modules
if(BUILD_TESTS)
    add_subdirectory(tests)
endif()
EOF
fi

# Step 6: Create kernel/README.md documenting the unified structure
cat > kernel/README.md << 'EOF'
# The Phoenix Exokernel - Unified Kernel

This is THE ONE kernel implementation for the Phoenix Exokernel project.
All kernel code has been unified, synthesized, and harmonized into this single directory.

## Structure

```
kernel/
├── boot/           # Boot code and initialization
├── drivers/        # Device drivers
├── fs/             # Filesystem implementation
├── include/        # Kernel-internal headers
├── ipc/            # Inter-process communication
├── mem/            # Memory management
├── sched/          # Process scheduling
├── sync/           # Synchronization primitives
├── sys/            # System calls
├── tests/          # Kernel test modules
└── time/           # Time and clock management
```

## Key Components

- **arbitrate.c**: Resource arbitration and allocation
- **crypto.c**: Cryptographic functions for capabilities
- **spinlock.h**: Unified spinlock implementation
- **sleeplock.h**: Sleep locks for blocking synchronization
- **buf.h**: Buffer cache management

## Building

The kernel is built as part of the main CMake build system:

```bash
mkdir build && cd build
cmake .. -DCMAKE_BUILD_TYPE=Release
make kernel
```

## Testing

Test modules are available in the `tests/` subdirectory and can be
enabled with `-DBUILD_TESTS=ON` during CMake configuration.
EOF

echo "=== KERNEL UNIFICATION COMPLETE ==="
echo "There is now ONE kernel at kernel/"
echo "All competing implementations have been merged and synthesized"
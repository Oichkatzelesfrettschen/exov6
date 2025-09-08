#!/bin/bash
# Repository Reorganization Script
# This script merges, harmonizes, and synthesizes the ExoV6 repository structure

set -e

echo "=== ExoV6 Repository Reorganization ==="
echo "Phase 1: Backup and preparation"

# Create backup
if [ ! -d "../exov6_backup_$(date +%Y%m%d)" ]; then
    echo "Creating backup..."
    cp -r . "../exov6_backup_$(date +%Y%m%d)"
fi

echo "Phase 2: Remove redundant engine directory"
# The engine directory is a duplicate of the main structure
if [ -d "engine" ]; then
    echo "Removing engine directory (duplicate content)..."
    git rm -rf engine/ 2>/dev/null || rm -rf engine/
fi

echo "Phase 3: Move misplaced root files"
# Move misplaced C files to appropriate directories
[ -f "hello.c" ] && git mv hello.c demos/hello.c 2>/dev/null || mv hello.c demos/hello.c 2>/dev/null || true
[ -f "hello_kernel.c" ] && git mv hello_kernel.c demos/hello_kernel.c 2>/dev/null || mv hello_kernel.c demos/hello_kernel.c 2>/dev/null || true
[ -f "integrate_tests.c" ] && git mv integrate_tests.c tests/c17/integrate_tests.c 2>/dev/null || mv integrate_tests.c tests/c17/integrate_tests.c 2>/dev/null || true
[ -f "kernel_stub.c" ] && git mv kernel_stub.c kernel/stubs/kernel_stub.c 2>/dev/null || mv kernel_stub.c kernel/stubs/kernel_stub.c 2>/dev/null || true
[ -f "shell_comprehensive.c" ] && git mv shell_comprehensive.c user/shell_comprehensive.c 2>/dev/null || mv shell_comprehensive.c user/shell_comprehensive.c 2>/dev/null || true
[ -f "shell_support.c" ] && git mv shell_support.c user/shell_support.c 2>/dev/null || mv shell_support.c user/shell_support.c 2>/dev/null || true
[ -f "shell_architecture.h" ] && git mv shell_architecture.h include/shell_architecture.h 2>/dev/null || mv shell_architecture.h include/shell_architecture.h 2>/dev/null || true
[ -f "user_minimal.h" ] && git mv user_minimal.h include/user_minimal.h 2>/dev/null || mv user_minimal.h include/user_minimal.h 2>/dev/null || true

# Clean up build artifacts from root
echo "Cleaning build artifacts from root..."
rm -f *.o *.d 2>/dev/null || true
[ -f "bootblock.asm" ] && git mv bootblock.asm kernel/boot/bootblock.asm 2>/dev/null || mv bootblock.asm kernel/boot/bootblock.asm 2>/dev/null || true
[ -f "bootblock 2.asm" ] && rm -f "bootblock 2.asm" 2>/dev/null || true

echo "Phase 4: Consolidate headers"
# Remove duplicate spinlock headers, keeping the kernel version
[ -f "libos/spinlock.h" ] && rm -f libos/spinlock.h 2>/dev/null || true
[ -f "include/libos/spinlock.h" ] && rm -f include/libos/spinlock.h 2>/dev/null || true

# Ensure single stat.h location
[ -f "kernel/stat.h" ] && rm -f kernel/stat.h 2>/dev/null || true

# Clean up duplicate fs.h
[ -f "libos/fs.h" ] && rm -f libos/fs.h 2>/dev/null || true

echo "Phase 5: Create directory structure for C17 tests"
mkdir -p tests/c17/{unit,integration,performance,posix}

echo "Phase 6: Remove test_isolation directory (POSIX test suite)"
# This is a massive external test suite that should be a submodule
if [ -d "test_isolation" ]; then
    echo "Removing test_isolation (should be external dependency)..."
    git rm -rf test_isolation/ 2>/dev/null || rm -rf test_isolation/
fi

echo "Phase 7: Clean up minimal_kernel (moved to demos)"
if [ -d "minimal_kernel" ]; then
    [ ! -d "demos/minimal_kernel" ] && mkdir -p demos/minimal_kernel
    cp -r minimal_kernel/* demos/minimal_kernel/ 2>/dev/null || true
    git rm -rf minimal_kernel/ 2>/dev/null || rm -rf minimal_kernel/
fi

echo "=== Reorganization Complete ==="
echo "Next steps:"
echo "1. Convert Python tests to C17"
echo "2. Update CMakeLists.txt for new structure"
echo "3. Commit the changes"
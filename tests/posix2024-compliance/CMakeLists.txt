# POSIX 2024 Compliance Test Suite
cmake_minimum_required(VERSION 3.16)

# C17 standard enforcement for POSIX 2024 compliance
set(CMAKE_C_STANDARD 17)
set(CMAKE_C_STANDARD_REQUIRED ON)
set(CMAKE_C_EXTENSIONS OFF)

# Compiler flags for POSIX compatibility tests
set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} -Wall -Wextra")
set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} -D_POSIX_C_SOURCE=200809L")
set(CMAKE_C_FLAGS_DEBUG "-g -O0")
set(CMAKE_C_FLAGS_RELEASE "-O2")

# NOTE: The full POSIX compatibility test (test_posix_compatibility.c) requires
# kernel infrastructure that conflicts with host glibc:
# - kernel/sys/syscall_gateway.h includes x86.h which conflicts with arch_x86_64.h
# - kernel/sys/syscall_posix2024.h depends on kernel struct definitions
# - libos/posix2024/stdio.h defines FILE that conflicts with glibc
#
# This test is disabled until a proper QEMU-based kernel test harness is available.
# For now, the test infrastructure only validates that the build system works.

message(STATUS "POSIX 2024 compliance test: DISABLED (requires QEMU kernel test harness)")
message(STATUS "  - Full kernel integration tests require running in QEMU")
message(STATUS "  - See docs/testing/QEMU-TESTING.md for kernel test instructions")

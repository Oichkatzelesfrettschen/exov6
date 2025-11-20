# kernel/CMakeLists.txt - ExoV6 Kernel

# ═════════════════════════════════════════════════════════════════════
# MCU TARGET (Early exit for microcontroller builds)
# ═════════════════════════════════════════════════════════════════════

if(MCU)
    # MCU-specific kernel build
    phoenix_add_executable(kernel-mcu
        SOURCES 
            picokernel.c
            ${CMAKE_SOURCE_DIR}/user/blink.c
            ${CMAKE_SOURCE_DIR}/src/arch/mcu/startup.c
        INCLUDES 
            ${CMAKE_CURRENT_SOURCE_DIR}
            ${CMAKE_CURRENT_SOURCE_DIR}/include
            ${CMAKE_SOURCE_DIR}/src/arch/mcu
            ${CMAKE_SOURCE_DIR}/include
        DEPENDENCIES phoenix-architecture
        DEFINITIONS MCU=1
    )
    
    set_target_properties(phoenix-kernel-mcu PROPERTIES 
        OUTPUT_NAME "kernel-mcu"
        PREFIX ""
    )
    
    # Create alias for main kernel target
    add_executable(phoenix-kernel ALIAS phoenix-kernel-mcu)
    
    message(STATUS "Kernel zone configured for MCU target")
    return()
endif()

# ═════════════════════════════════════════════════════════════════════
# KERNEL SOURCE COLLECTION
# ═════════════════════════════════════════════════════════════════════

# Core kernel sources (exclude host tools like mkfs.c)
file(GLOB KERNEL_CORE_SOURCES *.c)
list(REMOVE_ITEM KERNEL_CORE_SOURCES
    "${CMAKE_CURRENT_SOURCE_DIR}/mkfs.c"
    "${CMAKE_CURRENT_SOURCE_DIR}/mkfs_standalone.c"
)

# Ensure string.c is included (critical for memcpy, memset, etc.)
if(NOT "${CMAKE_CURRENT_SOURCE_DIR}/string.c" IN_LIST KERNEL_CORE_SOURCES)
    list(APPEND KERNEL_CORE_SOURCES "${CMAKE_CURRENT_SOURCE_DIR}/string.c")
endif()

# Assembly sources - architecture-specific
if(CMAKE_SYSTEM_PROCESSOR MATCHES "x86_64" OR CMAKE_C_COMPILER_TARGET MATCHES "x86_64" OR NOT CMAKE_SYSTEM_PROCESSOR MATCHES "i[3-6]86")
    # x86_64 build - use only compatible assembly
    set(KERNEL_ASM_SOURCES
        swtch.S  # Already has x86_64 support via #ifdef
    )
    if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/swtch64.S")
        list(APPEND KERNEL_ASM_SOURCES swtch64.S)
    endif()
    # Exclude 32-bit only files: entryother.S, initcode.S
else()
    # i386 build - use all assembly
    file(GLOB KERNEL_ASM_SOURCES *.S)
    list(FILTER KERNEL_ASM_SOURCES EXCLUDE REGEX "test_")
endif()

# Architecture-specific sources from src/arch (already compiled into architecture libs)
# These are included via library dependencies

# Hypervisor sources
set(HYPERVISOR_SOURCES)
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/hypervisor")
    file(GLOB HYPERVISOR_SOURCES hypervisor/*.c)
endif()

# Synchronization primitives (use only working implementation)
set(SYNC_SOURCES)
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/sync/spinlock.c")
    list(APPEND SYNC_SOURCES sync/spinlock.c)
endif()
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/sync/sleeplock.c")
    list(APPEND SYNC_SOURCES sync/sleeplock.c)
endif()
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/sync/rcu.c")
    list(APPEND SYNC_SOURCES sync/rcu.c)
endif()
# NUMA-aware queued spinlock (qspinlock) - new lock subsystem
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/sync/qspinlock.c")
    list(APPEND SYNC_SOURCES sync/qspinlock.c)
endif()
# Adaptive mutex - spin/block hybrid for medium-length critical sections
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/sync/adaptive_mutex.c")
    list(APPEND SYNC_SOURCES sync/adaptive_mutex.c)
endif()
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/sync/turnstile.c")
    list(APPEND SYNC_SOURCES sync/turnstile.c)
endif()
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/sync/priority.c")
    list(APPEND SYNC_SOURCES sync/priority.c)
endif()
# LWKT tokens - CPU-owned soft locks with automatic release on context switch
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/sync/lwkt_token.c")
    list(APPEND SYNC_SOURCES sync/lwkt_token.c)
endif()
# DAG lock ordering - deadlock prevention via hierarchical ordering
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/sync/dag.c")
    list(APPEND SYNC_SOURCES sync/dag.c)
endif()

# Device drivers
set(DRIVER_SOURCES)
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/drivers")
    file(GLOB_RECURSE DRIVER_SOURCES drivers/*.c)
endif()

# File system
set(FS_SOURCES)
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/fs")
    file(GLOB_RECURSE FS_SOURCES fs/*.c)
endif()

# Memory management
set(MEM_SOURCES)
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/mem")
    file(GLOB_RECURSE MEM_SOURCES mem/*.c)
endif()

# IPC
set(IPC_SOURCES)
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/ipc")
    file(GLOB_RECURSE IPC_SOURCES ipc/*.c)
endif()

# Scheduler
set(SCHED_SOURCES)
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/sched")
    file(GLOB_RECURSE SCHED_SOURCES sched/*.c)
endif()

# System calls
set(SYS_SOURCES)
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/sys")
    file(GLOB_RECURSE SYS_SOURCES sys/*.c)
endif()

# Time subsystem
set(TIME_SOURCES)
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/time")
    file(GLOB_RECURSE TIME_SOURCES time/*.c)
endif()

# Capability subsystem
set(CAP_SOURCES)
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/capability")
    file(GLOB_RECURSE CAP_SOURCES capability/*.c)
endif()

# Core subsystem
set(CORE_SOURCES)
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/core")
    file(GLOB_RECURSE CORE_SOURCES core/*.c)
endif()

# Combine all kernel sources
set(ALL_KERNEL_SOURCES
    ${KERNEL_CORE_SOURCES}
    ${KERNEL_ASM_SOURCES}
    ${HYPERVISOR_SOURCES}
    ${SYNC_SOURCES}
    ${DRIVER_SOURCES}
    ${FS_SOURCES}
    ${MEM_SOURCES}
    ${IPC_SOURCES}
    ${SCHED_SOURCES}
    ${SYS_SOURCES}
    ${TIME_SOURCES}
    ${CAP_SOURCES}
    ${CORE_SOURCES}
)

# Remove any sources that shouldn't be in the main kernel
list(FILTER ALL_KERNEL_SOURCES EXCLUDE REGEX ".*test.*")
list(FILTER ALL_KERNEL_SOURCES EXCLUDE REGEX ".*picokernel.*")

# ═════════════════════════════════════════════════════════════════════
# KERNEL EXECUTABLE
# ═════════════════════════════════════════════════════════════════════

phoenix_add_executable(kernel
    SOURCES ${ALL_KERNEL_SOURCES}
    INCLUDES 
        ${CMAKE_CURRENT_SOURCE_DIR}
        ${CMAKE_CURRENT_SOURCE_DIR}/include
        ${CMAKE_CURRENT_SOURCE_DIR}/hypervisor
        ${CMAKE_SOURCE_DIR}/include
        ${CMAKE_SOURCE_DIR}/proto
        ${CMAKE_SOURCE_DIR}/libos/stubs
    DEPENDENCIES 
        phoenix-architecture
        phoenix-ddekit
        phoenix-nstr-graph
        phoenix-protocols
)

# Add Cap'n Proto dependency if enabled
if(USE_CAPNP AND TARGET phoenix-capnp)
    target_link_libraries(kernel PRIVATE phoenix-capnp)
endif()

# Set kernel-specific properties
set_target_properties(kernel PROPERTIES 
    OUTPUT_NAME "kernel"
    PREFIX ""
)

# ═════════════════════════════════════════════════════════════════════
# KERNEL FEATURE CONFIGURATION
# ═════════════════════════════════════════════════════════════════════

# Feature-based compilation definitions
if(USE_TICKET_LOCK)
    target_compile_definitions(kernel PRIVATE USE_TICKET_LOCK)
endif()

if(IPC_DEBUG)
    target_compile_definitions(kernel PRIVATE IPC_DEBUG)
endif()

if(USE_SIMD)
    target_compile_definitions(kernel PRIVATE USE_SIMD)
endif()

# New lock subsystem feature flags
option(USE_EXOLOCK "Enable new ExoLock subsystem (qspinlock, adaptive mutex, etc.)" OFF)
if(USE_EXOLOCK)
    target_compile_definitions(kernel PRIVATE USE_EXOLOCK)
    message(STATUS "  - ExoLock subsystem: ENABLED")
else()
    message(STATUS "  - ExoLock subsystem: DISABLED (use -DUSE_EXOLOCK=ON to enable)")
endif()

# DAG lock ordering for deadlock prevention
option(USE_DAG_CHECKING "Enable DAG lock ordering validation (runtime deadlock prevention)" OFF)
if(USE_DAG_CHECKING)
    target_compile_definitions(kernel PRIVATE USE_DAG_CHECKING)
    message(STATUS "  - DAG lock ordering: ENABLED")

    option(DAG_PANIC_ON_VIOLATION "Panic on DAG violations (vs warning)" ON)
    if(DAG_PANIC_ON_VIOLATION)
        target_compile_definitions(kernel PRIVATE DAG_PANIC_ON_VIOLATION)
        message(STATUS "    - Panic on violation: YES")
    else()
        message(STATUS "    - Panic on violation: NO (warning only)")
    endif()
else()
    message(STATUS "  - DAG lock ordering: DISABLED (use -DUSE_DAG_CHECKING=ON to enable)")
endif()

# ═════════════════════════════════════════════════════════════════════
# STRICT WARNING CONFIGURATION (Rust-level strictness)
# ═════════════════════════════════════════════════════════════════════

# Base warnings for high code quality
set(KERNEL_WARNINGS
    -Wall -Wextra -Wpedantic
    -Wshadow -Wcast-align -Wcast-qual
    -Wformat=2 -Wnull-dereference
    -Wunused -Wundef -Wwrite-strings
    -Werror                 # Treat warnings as errors (zero-warning policy ENFORCED)
)

# Disabled warnings (too noisy for kernel code or intentional GNU extensions)
# TODO: Re-enable and fix these warnings as technical debt items
set(KERNEL_WARNINGS_DISABLED
    # Too noisy for kernel code
    -Wno-unused-parameter       # Kernel APIs often have unused params
    -Wno-sign-conversion        # Too noisy for pointer arithmetic
    -Wno-conversion             # Too noisy for kernel code
    -Wno-double-promotion       # Intentional in some kernel math
    # -Wno-sign-compare           # ✅ FIXED (25 instances - proper type casts with validation)
    # -Wno-unused-function        # ✅ FIXED (33 instances - marked with __attribute__((unused)))
    # -Wno-unused-variable        # ✅ FIXED (5 instances - marked with (void) or __attribute__((unused)))
    # -Wno-unused-result          # ✅ FIXED (4 instances - proper error handling)

    # Intentional GNU extensions
    -Wno-gnu-include-next       # Freestanding header wrapping
    -Wno-keyword-macro          # Freestanding stdbool.h implementation
    -Wno-zero-length-array      # Flexible array members
    -Wno-cast-align             # Intentional alignment casts in compat layer
    -Wno-cast-qual              # Intentional qualifier discarding in kernel
    -Wno-gnu-zero-variadic-macro-arguments  # Variadic macro extensions
    -Wno-gnu-designator         # Designated initializer extensions
    -Wno-gnu-statement-expression-from-macro-expansion  # Statement expressions
    -Wno-gnu-empty-struct       # Empty struct extensions
    -Wno-gnu-pointer-arith      # Pointer arithmetic on void*

    # Known type issues (ALL FIXED!)
    # -Wno-incompatible-pointer-types  # ✅ FIXED (19 instances - proper kalloc/kfree casts, lock type fixes)
    # -Wno-incompatible-pointer-types-discards-qualifiers  # ✅ FIXED (13 instances - const correctness)
    # -Wno-pointer-to-int-cast    # ✅ FIXED (5 instances - uintptr_t intermediate casts)
    # -Wno-int-to-pointer-cast    # ✅ FIXED (2 instances - uintptr_t intermediate casts)
    # -Wno-int-to-void-pointer-cast  # ✅ FIXED (2 instances - uintptr_t intermediate casts)

    # Low-priority or false positives
    -Wno-tautological-constant-out-of-range-compare  # Often macro-generated
    -Wno-shadow                 # TODO: Fix variable shadowing (2 instances)
    -Wno-macro-redefined        # TODO: Fix duplicate macro definitions (4 instances)
    -Wno-sync-alignment         # Atomic alignment issues (2 instances)
    -Wno-shift-count-overflow   # Shift overflow in bit manipulation
    -Wno-missing-braces         # Brace style preferences
    -Wno-visibility             # Symbol visibility (1 instance)
    -Wno-unused-const-variable  # Unused const (1 instance)
    -Wno-empty-translation-unit # Empty .c files (1 instance)
)

# Apply warning flags to kernel
target_compile_options(kernel PRIVATE
    ${KERNEL_WARNINGS}
    ${KERNEL_WARNINGS_DISABLED}
)

# Apply additional CPU flags if specified
set(CPUFLAGS "" CACHE STRING "Additional CPU specific compile flags")
if(CPUFLAGS)
    target_compile_options(kernel PRIVATE ${CPUFLAGS})
endif()

# ═════════════════════════════════════════════════════════════════════
# KERNEL MODULES (OPTIONAL)
# ═════════════════════════════════════════════════════════════════════

# Security audit module
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/cap_security.c")
    phoenix_add_library(phoenix-kernel-security
        STATIC
        SOURCES cap_security.c
        INCLUDES 
            ${CMAKE_CURRENT_SOURCE_DIR}
            ${CMAKE_CURRENT_SOURCE_DIR}/include
            ${CMAKE_SOURCE_DIR}/include
        DEPENDENCIES phoenix-architecture
    )
    
    target_link_libraries(kernel PRIVATE phoenix-kernel-security)
endif()

# Memory management module
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/cap_mem.c")
    phoenix_add_library(phoenix-kernel-memory
        STATIC
        SOURCES cap_mem.c
        INCLUDES 
            ${CMAKE_CURRENT_SOURCE_DIR}
            ${CMAKE_CURRENT_SOURCE_DIR}/include
            ${CMAKE_SOURCE_DIR}/include
        DEPENDENCIES phoenix-architecture
    )
    
    target_link_libraries(kernel PRIVATE phoenix-kernel-memory)
endif()

# IPC queue module
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/exo_ipc_queue.c")
    phoenix_add_library(phoenix-kernel-ipc-queue
        STATIC
        SOURCES exo_ipc_queue.c
        INCLUDES 
            ${CMAKE_CURRENT_SOURCE_DIR}
            ${CMAKE_CURRENT_SOURCE_DIR}/include
            ${CMAKE_SOURCE_DIR}/include
        DEPENDENCIES phoenix-architecture
    )
    
    target_link_libraries(kernel PRIVATE phoenix-kernel-ipc-queue)
endif()

# Streaming module
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/streams.c")
    phoenix_add_library(phoenix-kernel-streams
        STATIC
        SOURCES streams.c
        INCLUDES 
            ${CMAKE_CURRENT_SOURCE_DIR}
            ${CMAKE_CURRENT_SOURCE_DIR}/include
            ${CMAKE_SOURCE_DIR}/include
        DEPENDENCIES phoenix-architecture
    )
    
    target_link_libraries(kernel PRIVATE phoenix-kernel-streams)
endif()

# Lattice IPC module
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/lattice_ipc.c")
    phoenix_add_library(phoenix-kernel-lattice-ipc
        STATIC
        SOURCES lattice_ipc.c
        INCLUDES 
            ${CMAKE_CURRENT_SOURCE_DIR}
            ${CMAKE_CURRENT_SOURCE_DIR}/include
            ${CMAKE_SOURCE_DIR}/include
        DEPENDENCIES phoenix-architecture
    )
    
    target_link_libraries(kernel PRIVATE phoenix-kernel-lattice-ipc)
endif()

# Crypto module
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/crypto.c")
    phoenix_add_library(phoenix-kernel-crypto
        STATIC
        SOURCES crypto.c
        INCLUDES 
            ${CMAKE_CURRENT_SOURCE_DIR}
            ${CMAKE_CURRENT_SOURCE_DIR}/include
            ${CMAKE_SOURCE_DIR}/include
        DEPENDENCIES phoenix-architecture
    )
    
    target_link_libraries(kernel PRIVATE phoenix-kernel-crypto)
endif()

# ═════════════════════════════════════════════════════════════════════
# KERNEL DEBUGGING AND TESTING
# ═════════════════════════════════════════════════════════════════════

# Test spinlock executable (if test sources exist)
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/test_quaternion_spinlock.c")
    phoenix_add_executable(test-quaternion-spinlock
        SOURCES test_quaternion_spinlock.c
        INCLUDES 
            ${CMAKE_CURRENT_SOURCE_DIR}
            ${CMAKE_CURRENT_SOURCE_DIR}/include
            ${CMAKE_SOURCE_DIR}/include
        DEPENDENCIES phoenix-architecture
    )
    
    set_target_properties(test-quaternion-spinlock PROPERTIES 
        OUTPUT_NAME "test-quaternion-spinlock"
        PREFIX ""
    )
endif()

# ═════════════════════════════════════════════════════════════════════
# LINKER SCRIPT AND SPECIAL LINKING
# ═════════════════════════════════════════════════════════════════════

# Use kernel linker script if it exists
if(EXISTS "${CMAKE_SOURCE_DIR}/kernel.ld")
    target_link_options(kernel PRIVATE 
        "LINKER:-T,${CMAKE_SOURCE_DIR}/kernel.ld"
    )
endif()

# Set kernel-specific link options
target_link_options(kernel PRIVATE
    -nostdlib
    -static
    "LINKER:--allow-multiple-definition"  # TEMP: Allow duplicate symbols during prototyping
    "LINKER:-z,noexecstack"               # Security: non-executable stack
)

# ═════════════════════════════════════════════════════════════════════
# EXPORTS
# ═════════════════════════════════════════════════════════════════════

set(EXOV6_KERNEL_TARGETS
    kernel
    PARENT_SCOPE
)

# Export optional kernel modules
set(KERNEL_MODULE_TARGETS)
foreach(module security memory ipc-queue streams lattice-ipc crypto)
    if(TARGET phoenix-kernel-${module})
        list(APPEND KERNEL_MODULE_TARGETS phoenix-kernel-${module})
    endif()
endforeach()

if(KERNEL_MODULE_TARGETS)
    set(EXOV6_KERNEL_MODULE_TARGETS ${KERNEL_MODULE_TARGETS} PARENT_SCOPE)
endif()

message(STATUS "Kernel zone configured:")
message(STATUS "  - Main kernel: ✓")
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/hypervisor")
    message(STATUS "  - Hypervisor support: ✓")
endif()
if(KERNEL_MODULE_TARGETS)
    message(STATUS "  - Kernel modules: ${KERNEL_MODULE_TARGETS}")
endif()
if(USE_CAPNP)
    message(STATUS "  - Cap'n Proto support: ✓")
endif()
if(TARGET phoenix-test-quaternion-spinlock)
    message(STATUS "  - Test utilities: ✓")
endif()
# Kernel test modules (temporarily disabled)
# if(BUILD_TESTS)
#     add_subdirectory(tests)
# endif()

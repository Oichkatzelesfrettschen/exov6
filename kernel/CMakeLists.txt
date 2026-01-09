# kernel/CMakeLists.txt - ExoV6 Kernel

# ═════════════════════════════════════════════════════════════════════
# MCU TARGET (Early exit for microcontroller builds)
# ═════════════════════════════════════════════════════════════════════

if(MCU)
    # MCU-specific kernel build
    feuerbird_add_executable(kernel-mcu
        SOURCES 
            picokernel.c
            ${CMAKE_SOURCE_DIR}/user/blink.c
            ${CMAKE_SOURCE_DIR}/src/arch/mcu/startup.c
        INCLUDES 
            ${CMAKE_CURRENT_SOURCE_DIR}
            ${CMAKE_CURRENT_SOURCE_DIR}/include
            ${CMAKE_SOURCE_DIR}/src/arch/mcu
            ${CMAKE_SOURCE_DIR}/include
        DEPENDENCIES feuerbird-architecture
        DEFINITIONS MCU=1
    )
    
    set_target_properties(feuerbird-kernel-mcu PROPERTIES 
        OUTPUT_NAME "kernel-mcu"
        PREFIX ""
    )
    
    # Create alias for main kernel target
    add_executable(feuerbird-kernel ALIAS feuerbird-kernel-mcu)
    
    message(STATUS "Kernel zone configured for MCU target")
    return()
endif()

# ═════════════════════════════════════════════════════════════════════
# KERNEL SOURCE COLLECTION
# ═════════════════════════════════════════════════════════════════════

# Core kernel sources (top-level)
file(GLOB KERNEL_CORE_SOURCES *.c)

# Assembly sources
file(GLOB KERNEL_ASM_SOURCES *.S)

# Subdirectory sources - these contain the actual implementations
# NOTE: Most subdirs have conflicting type definitions with main kernel
# They need significant refactoring; for now, disable all subdirs and rely on
# architecture-layer implementations in src/arch
set(KERNEL_SYNC_SOURCES)
set(KERNEL_SCHED_SOURCES)
# IPC sources - capability table is required for core kernel functionality
# cap_table.c: capability table with epoch-based IDs (cap_table_alloc, cap_revoke, etc.)
# cap.c: SipHash-based capability authentication (cap_new, cap_verify)
# endpoint.c: DEFERRED TO PHASE 5 - depends on full syscall infrastructure (see below)
set(KERNEL_IPC_SOURCES
    ${CMAKE_CURRENT_SOURCE_DIR}/ipc/cap_table.c
    ${CMAKE_CURRENT_SOURCE_DIR}/ipc/cap.c
)
set(KERNEL_FS_SOURCES)
set(KERNEL_MEM_SOURCES)
set(KERNEL_CAPABILITY_SOURCES)
set(KERNEL_CORE_SUBDIR_SOURCES)
# System call infrastructure - PHASE 5 DEFERRAL
# Excluded: syscall.c contains a complete syscall dispatch table with ~60+ syscall handlers.
# Most handlers are not implemented yet (sys_fork, sys_exec, sys_open, sys_read, sys_write,
# sys_mappte, sys_exo_*, etc.). Integrating syscall.c creates linker errors for all missing
# handlers. In Phase 5A-5B, when exo_impl.c and other core syscall handlers are integrated,
# syscall.c can be safely compiled and will provide argument extraction (argptr, argint,
# argstr) for all syscalls. Until then, we rely on kernel_core_stubs.c minimal stubs.
# Dependencies for Phase 5 integration:
#   - Core syscall handlers from exo_impl.c (sys_exo_yield_to, sys_exo_alloc_page, etc.)
#   - File syscalls from fs layer (sys_open, sys_read, sys_write, sys_close, sys_stat)
#   - Process syscalls from sched (sys_fork, sys_exec, sys_exit, sys_wait)
#   - IPC syscalls (sys_endpoint_send, sys_endpoint_recv require endpoint.c)
#   - All other syscall handlers referenced in syscall.c dispatch table
# After Phase 5A, uncomment: ${CMAKE_CURRENT_SOURCE_DIR}/sys/syscall.c
set(KERNEL_SYS_SOURCES
)
set(KERNEL_DRIVERS_SOURCES)
set(KERNEL_TIME_SOURCES)
set(KERNEL_BOOT_SOURCES)
set(KERNEL_EXEC_SOURCES)

# 64-bit boot trampoline with multiboot2 support
# Linker script updated (2025-01) with:
# 1. Low-memory boot sections (.boot, .boot_text, .boot_data, .boot_bss)
# 2. Identity + high-half page table mapping in multiboot2.S
# 3. main64 entry point for 64-bit kernel handoff
if(CMAKE_SIZEOF_VOID_P EQUAL 8)
    # Add multiboot2 boot trampoline
    if(EXISTS "${CMAKE_SOURCE_DIR}/src/arch/x64/multiboot2.S")
        list(APPEND KERNEL_ASM_SOURCES "${CMAKE_SOURCE_DIR}/src/arch/x64/multiboot2.S")
    endif()
    # Add main64 entry point
    if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/boot/main64.c")
        list(APPEND KERNEL_BOOT_SOURCES "${CMAKE_CURRENT_SOURCE_DIR}/boot/main64.c")
    endif()
endif()

# Architecture-specific sources from src/arch (already compiled into architecture libs)
# These are included via library dependencies

# Hypervisor sources
set(HYPERVISOR_SOURCES)
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/hypervisor")
    file(GLOB HYPERVISOR_SOURCES hypervisor/*.c)
endif()

# Combine all kernel sources
set(ALL_KERNEL_SOURCES
    ${KERNEL_CORE_SOURCES}
    ${KERNEL_ASM_SOURCES}
    ${KERNEL_SYNC_SOURCES}
    ${KERNEL_SCHED_SOURCES}
    ${KERNEL_IPC_SOURCES}
    ${KERNEL_FS_SOURCES}
    ${KERNEL_MEM_SOURCES}
    ${KERNEL_CAPABILITY_SOURCES}
    ${KERNEL_CORE_SUBDIR_SOURCES}
    ${KERNEL_SYS_SOURCES}
    ${KERNEL_DRIVERS_SOURCES}
    ${KERNEL_TIME_SOURCES}
    ${KERNEL_BOOT_SOURCES}
    ${KERNEL_EXEC_SOURCES}
    ${HYPERVISOR_SOURCES}
)

# Remove any sources that shouldn't be in the main kernel
list(FILTER ALL_KERNEL_SOURCES EXCLUDE REGEX ".*test.*")
list(FILTER ALL_KERNEL_SOURCES EXCLUDE REGEX ".*picokernel.*")
list(FILTER ALL_KERNEL_SOURCES EXCLUDE REGEX ".*mkfs.*")
# Exclude q16 math files - use non-existent/SSE4.1+ SIMD intrinsics (needs proper SIMD detection)
list(FILTER ALL_KERNEL_SOURCES EXCLUDE REGEX ".*q16_octonion.*")
list(FILTER ALL_KERNEL_SOURCES EXCLUDE REGEX ".*q16_fixed.*")
# lambda_cap.c: COMPILATION FIXED (strlen, octonion.v->coeffs) 2025-01
# cap.c INTEGRATED (2025-01): cap_revoke, cap_table_remove now available
# q16_octonion INTEGRATED (2025-01): norm functions now inline in q16_octonion.h
# Lambda capability engine now included in kernel build
# Exclude 32-bit assembly files (use 64-bit variants for x86_64 builds)
if(CMAKE_SIZEOF_VOID_P EQUAL 8)
    list(FILTER ALL_KERNEL_SOURCES EXCLUDE REGEX ".*/swtch\\.S$")
endif()
# Zone allocator files - PHASE 5 DEFERRAL
# Excluded: stubs.c and zone.c have deep exokernel dependencies (cap_kalloc, pipewrite,
#           exo_send, exo_recv, exo_alloc_page) that require Phase 5 implementation
# Dependencies:
#   stubs.c: VFS operations (filealloc, fileread, filewrite) depend on exo_send/recv
#   zone.c: cap_kalloc() - capability-aware memory allocation (Phase 5)
# Integration blocked until exo_impl.c, capability_lattice.c are implemented
# Status: DISABLED until Phase 5 - exokernel substrate complete
list(FILTER ALL_KERNEL_SOURCES EXCLUDE REGEX ".*zone\\.c$")
# Zone isolation - PHASE 5 DEFERRAL
# Excluded: cap_validate_unified() requires full capability validation system
# Dependencies: cap_validate_unified() implementation in ipc/cap.c or capability/
# Note: Header fixed (vm.h->memlayout.h, cap.h updated), but implementation incomplete
# Status: DISABLED until Phase 5 - capability lattice complete
list(FILTER ALL_KERNEL_SOURCES EXCLUDE REGEX ".*zone_isolation.*")
# Endpoint IPC - PHASE 5 DEFERRAL
# Excluded: endpoint.c syscall handlers (sys_endpoint_send, sys_endpoint_recv) require
#           full syscall infrastructure. Currently, syscall.c dispatch table is disabled
#           due to ~60+ unimplemented syscall handlers. In Phase 5A, when exo_impl.c,
#           file syscalls, process syscalls, and other handlers are implemented,
#           syscall.c can be integrated and endpoint.c becomes usable.
# Dependencies for Phase 5A integration:
#   - syscall.c: complete syscall dispatch table with argument extraction
#   - exo_impl.c: core exokernel syscall handlers (sys_exo_yield_to, sys_exo_alloc_page, etc.)
#   - File syscalls: sys_open, sys_read, sys_write, sys_close, sys_stat, etc.
#   - Process syscalls: sys_fork, sys_exec, sys_exit, sys_wait, etc.
# Note: endpoint.c IPC functions (endpoint_init, endpoint_send, endpoint_recv) are
#       complete, but syscall handlers cannot be used until full syscall layer exists
# Status: DISABLED until Phase 5A - full syscall infrastructure complete
list(FILTER ALL_KERNEL_SOURCES EXCLUDE REGEX ".*endpoint\\.c$")
# Exclude exo_impl.c - has struct/function pointer type mismatches
list(FILTER ALL_KERNEL_SOURCES EXCLUDE REGEX ".*exo_impl.*")
# stubs.c - PHASE 5 DEFERRAL
# Excluded: VFS operations (filealloc, fileread, filewrite, fileclose, filestat)
#           depend on exokernel primitives (exo_send, exo_recv, pipewrite, piperead,
#           iput, readi, writei, begin_op, end_op) not available until Phase 5
# Dependencies:
#   - exo_send/exo_recv: requires exo_impl.c, IPC infrastructure (Phase 5)
#   - pipe operations: requires full VFS layer with pipe support (Phase 5)
#   - file operations: requires inode system, filesystem layer (Phase 5)
# Integration blocked until Phase 5 - exokernel VFS substrate complete
# Status: DISABLED until Phase 5 - exokernel IPC and filesystem complete
list(FILTER ALL_KERNEL_SOURCES EXCLUDE REGEX ".*/stubs\\.c$")
# Exclude 16/32-bit assembly that conflicts with 64-bit kernel (multiple 'start' definitions)
list(FILTER ALL_KERNEL_SOURCES EXCLUDE REGEX ".*initcode\\.S$")
list(FILTER ALL_KERNEL_SOURCES EXCLUDE REGEX ".*entryother\\.S$")
list(FILTER ALL_KERNEL_SOURCES EXCLUDE REGEX ".*bootasm.*\\.S$")
# Exclude advanced sync files with conflicting type definitions (mcs_node, rcu_synchronize)
list(FILTER ALL_KERNEL_SOURCES EXCLUDE REGEX ".*ultimate_lock_integration.*")
list(FILTER ALL_KERNEL_SOURCES EXCLUDE REGEX ".*ultimate_lock_synthesis.*")
list(FILTER ALL_KERNEL_SOURCES EXCLUDE REGEX ".*genetic_lock_evolution.*")
list(FILTER ALL_KERNEL_SOURCES EXCLUDE REGEX ".*quantum_lock.*")
list(FILTER ALL_KERNEL_SOURCES EXCLUDE REGEX ".*unified_lock.*")
list(FILTER ALL_KERNEL_SOURCES EXCLUDE REGEX ".*zerocopy_cow_dag.*")
list(FILTER ALL_KERNEL_SOURCES EXCLUDE REGEX ".*waitchan.*")
# Exclude capnp files if Cap'n Proto not enabled
if(NOT USE_CAPNP)
    list(FILTER ALL_KERNEL_SOURCES EXCLUDE REGEX ".*capnp.*")
endif()
# Exclude IPC files with missing dependencies or type conflicts
# endpoint.c - PHASE 4B INTEGRATION COMPLETE
# Status: ENABLED - endpoint_send, endpoint_recv, sys_endpoint_send, sys_endpoint_recv available
# Dependencies satisfied: ksleep/wakeup declared, syscall entries in kernel/syscall.c
# Note: Global endpoint queue used (static global_ep); userspace integration in Phase 5
# list(FILTER ALL_KERNEL_SOURCES EXCLUDE REGEX ".*endpoint\\.c$")
list(FILTER ALL_KERNEL_SOURCES EXCLUDE REGEX ".*exo_ipc_queue\\.c$")
list(FILTER ALL_KERNEL_SOURCES EXCLUDE REGEX ".*lattice_ipc\\.c$")
list(FILTER ALL_KERNEL_SOURCES EXCLUDE REGEX ".*lattice_kernel\\.c$")
list(FILTER ALL_KERNEL_SOURCES EXCLUDE REGEX ".*serialization\\.c$")
list(FILTER ALL_KERNEL_SOURCES EXCLUDE REGEX ".*serialization_simple\\.c$")
list(FILTER ALL_KERNEL_SOURCES EXCLUDE REGEX ".*unified_channel\\.c$")
list(FILTER ALL_KERNEL_SOURCES EXCLUDE REGEX ".*unified_ipc\\.c$")
list(FILTER ALL_KERNEL_SOURCES EXCLUDE REGEX ".*zero_copy\\.c$")
# capability_lattice.c is in kernel/capability/ subdir (disabled, see lines 46-48)
# Exclusion retained for if/when subdirectory sources are re-enabled
list(FILTER ALL_KERNEL_SOURCES EXCLUDE REGEX ".*capability_lattice\\.c$")
# Exclude procfs - has dependency issues
list(FILTER ALL_KERNEL_SOURCES EXCLUDE REGEX ".*procfs\\.c$")

# ═════════════════════════════════════════════════════════════════════
# KERNEL EXECUTABLE
# ═════════════════════════════════════════════════════════════════════

feuerbird_add_executable(kernel
    SOURCES ${ALL_KERNEL_SOURCES}
    INCLUDES
        ${CMAKE_CURRENT_SOURCE_DIR}
        ${CMAKE_CURRENT_SOURCE_DIR}/include
        ${CMAKE_CURRENT_SOURCE_DIR}/hypervisor
        ${CMAKE_CURRENT_SOURCE_DIR}/sync
        ${CMAKE_CURRENT_SOURCE_DIR}/sched
        ${CMAKE_CURRENT_SOURCE_DIR}/ipc
        ${CMAKE_CURRENT_SOURCE_DIR}/fs
        ${CMAKE_CURRENT_SOURCE_DIR}/mem
        ${CMAKE_CURRENT_SOURCE_DIR}/capability
        ${CMAKE_CURRENT_SOURCE_DIR}/core
        ${CMAKE_CURRENT_SOURCE_DIR}/sys
        ${CMAKE_CURRENT_SOURCE_DIR}/drivers
        ${CMAKE_CURRENT_SOURCE_DIR}/time
        ${CMAKE_CURRENT_SOURCE_DIR}/boot
        ${CMAKE_CURRENT_SOURCE_DIR}/exec
        ${CMAKE_SOURCE_DIR}/include
        ${CMAKE_SOURCE_DIR}/proto
        ${CMAKE_SOURCE_DIR}/libos/stubs
    DEPENDENCIES
        feuerbird-architecture
        feuerbird-ddekit
        feuerbird-nstr-graph
        feuerbird-protocols
)

# Add Cap'n Proto dependency if enabled
if(USE_CAPNP AND TARGET feuerbird-capnp)
    target_link_libraries(kernel PRIVATE feuerbird-capnp)
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
# EXO_KERNEL: Indicates kernel build context for conditional compilation
# - Disables floating-point octonion operations in lambda_cap.c
# - Uses fixed-point Q16.16 octonion math instead
target_compile_definitions(kernel PRIVATE EXO_KERNEL)

if(USE_TICKET_LOCK)
    target_compile_definitions(kernel PRIVATE USE_TICKET_LOCK)
endif()

if(IPC_DEBUG)
    target_compile_definitions(kernel PRIVATE IPC_DEBUG)
endif()

if(USE_SIMD)
    target_compile_definitions(kernel PRIVATE USE_SIMD)
endif()

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
    feuerbird_add_library(feuerbird-kernel-security
        STATIC
        SOURCES cap_security.c
        INCLUDES 
            ${CMAKE_CURRENT_SOURCE_DIR}
            ${CMAKE_CURRENT_SOURCE_DIR}/include
            ${CMAKE_SOURCE_DIR}/include
        DEPENDENCIES feuerbird-architecture
    )
    
    target_link_libraries(kernel PRIVATE feuerbird-kernel-security)
endif()

# Memory management module
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/cap_mem.c")
    feuerbird_add_library(feuerbird-kernel-memory
        STATIC
        SOURCES cap_mem.c
        INCLUDES 
            ${CMAKE_CURRENT_SOURCE_DIR}
            ${CMAKE_CURRENT_SOURCE_DIR}/include
            ${CMAKE_SOURCE_DIR}/include
        DEPENDENCIES feuerbird-architecture
    )
    
    target_link_libraries(kernel PRIVATE feuerbird-kernel-memory)
endif()

# IPC queue module
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/exo_ipc_queue.c")
    feuerbird_add_library(feuerbird-kernel-ipc-queue
        STATIC
        SOURCES exo_ipc_queue.c
        INCLUDES 
            ${CMAKE_CURRENT_SOURCE_DIR}
            ${CMAKE_CURRENT_SOURCE_DIR}/include
            ${CMAKE_SOURCE_DIR}/include
        DEPENDENCIES feuerbird-architecture
    )
    
    target_link_libraries(kernel PRIVATE feuerbird-kernel-ipc-queue)
endif()

# Streaming module
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/streams.c")
    feuerbird_add_library(feuerbird-kernel-streams
        STATIC
        SOURCES streams.c
        INCLUDES 
            ${CMAKE_CURRENT_SOURCE_DIR}
            ${CMAKE_CURRENT_SOURCE_DIR}/include
            ${CMAKE_SOURCE_DIR}/include
        DEPENDENCIES feuerbird-architecture
    )
    
    target_link_libraries(kernel PRIVATE feuerbird-kernel-streams)
endif()

# Lattice IPC module
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/lattice_ipc.c")
    feuerbird_add_library(feuerbird-kernel-lattice-ipc
        STATIC
        SOURCES lattice_ipc.c
        INCLUDES 
            ${CMAKE_CURRENT_SOURCE_DIR}
            ${CMAKE_CURRENT_SOURCE_DIR}/include
            ${CMAKE_SOURCE_DIR}/include
        DEPENDENCIES feuerbird-architecture
    )
    
    target_link_libraries(kernel PRIVATE feuerbird-kernel-lattice-ipc)
endif()

# Crypto module
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/crypto.c")
    feuerbird_add_library(feuerbird-kernel-crypto
        STATIC
        SOURCES crypto.c
        INCLUDES 
            ${CMAKE_CURRENT_SOURCE_DIR}
            ${CMAKE_CURRENT_SOURCE_DIR}/include
            ${CMAKE_SOURCE_DIR}/include
        DEPENDENCIES feuerbird-architecture
    )
    
    target_link_libraries(kernel PRIVATE feuerbird-kernel-crypto)
endif()

# ═════════════════════════════════════════════════════════════════════
# KERNEL DEBUGGING AND TESTING
# ═════════════════════════════════════════════════════════════════════

# Test spinlock executable (if test sources exist)
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/test_quaternion_spinlock.c")
    feuerbird_add_executable(test-quaternion-spinlock
        SOURCES test_quaternion_spinlock.c
        INCLUDES 
            ${CMAKE_CURRENT_SOURCE_DIR}
            ${CMAKE_CURRENT_SOURCE_DIR}/include
            ${CMAKE_SOURCE_DIR}/include
        DEPENDENCIES feuerbird-architecture
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
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/kernel.ld")
    target_link_options(kernel PRIVATE 
        "LINKER:-T,${CMAKE_CURRENT_SOURCE_DIR}/kernel.ld"
    )
endif()

# Set kernel-specific link options
target_link_options(kernel PRIVATE
    -nostdlib
    -static
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
    if(TARGET feuerbird-kernel-${module})
        list(APPEND KERNEL_MODULE_TARGETS feuerbird-kernel-${module})
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
if(TARGET feuerbird-test-quaternion-spinlock)
    message(STATUS "  - Test utilities: ✓")
endif()
# Kernel test modules (temporarily disabled)
# if(BUILD_TESTS)
#     add_subdirectory(tests)
# endif()

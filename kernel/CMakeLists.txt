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
set(KERNEL_IPC_SOURCES)
set(KERNEL_FS_SOURCES)
set(KERNEL_MEM_SOURCES)
set(KERNEL_CAPABILITY_SOURCES)
set(KERNEL_CORE_SUBDIR_SOURCES)
set(KERNEL_SYS_SOURCES)
set(KERNEL_DRIVERS_SOURCES)
set(KERNEL_TIME_SOURCES)
set(KERNEL_BOOT_SOURCES)
set(KERNEL_EXEC_SOURCES)

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
# Exclude lambda_cap.c - has symbol conflicts (strlen redefinition) and struct mismatches
list(FILTER ALL_KERNEL_SOURCES EXCLUDE REGEX ".*lambda_cap.*")
# Exclude 32-bit assembly files (use 64-bit variants for x86_64 builds)
if(CMAKE_SIZEOF_VOID_P EQUAL 8)
    list(FILTER ALL_KERNEL_SOURCES EXCLUDE REGEX ".*/swtch\\.S$")
endif()
# Exclude zone allocator files - have type mismatches and missing headers (vm.h)
list(FILTER ALL_KERNEL_SOURCES EXCLUDE REGEX ".*zone\\.c$")
list(FILTER ALL_KERNEL_SOURCES EXCLUDE REGEX ".*zone_isolation.*")
# Exclude exo_impl.c - has struct/function pointer type mismatches
list(FILTER ALL_KERNEL_SOURCES EXCLUDE REGEX ".*exo_impl.*")
# Exclude stubs.c - has undeclared functions (kexit, ksleep)
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
list(FILTER ALL_KERNEL_SOURCES EXCLUDE REGEX ".*endpoint\\.c$")
list(FILTER ALL_KERNEL_SOURCES EXCLUDE REGEX ".*exo_ipc_queue\\.c$")
list(FILTER ALL_KERNEL_SOURCES EXCLUDE REGEX ".*lattice_ipc\\.c$")
list(FILTER ALL_KERNEL_SOURCES EXCLUDE REGEX ".*lattice_kernel\\.c$")
list(FILTER ALL_KERNEL_SOURCES EXCLUDE REGEX ".*serialization\\.c$")
list(FILTER ALL_KERNEL_SOURCES EXCLUDE REGEX ".*serialization_simple\\.c$")
list(FILTER ALL_KERNEL_SOURCES EXCLUDE REGEX ".*unified_channel\\.c$")
list(FILTER ALL_KERNEL_SOURCES EXCLUDE REGEX ".*unified_ipc\\.c$")
list(FILTER ALL_KERNEL_SOURCES EXCLUDE REGEX ".*zero_copy\\.c$")
# Exclude capability_lattice - needs refactoring
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

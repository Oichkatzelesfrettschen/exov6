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

# Core kernel sources
file(GLOB KERNEL_CORE_SOURCES *.c)

# Assembly sources
file(GLOB KERNEL_ASM_SOURCES *.S)

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
    ${HYPERVISOR_SOURCES}
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
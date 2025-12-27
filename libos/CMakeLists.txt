# libos/CMakeLists.txt - Library Operating System

# ═════════════════════════════════════════════════════════════════════
# CORE LIBOS SERVICES
# ═════════════════════════════════════════════════════════════════════

# File system service
feuerbird_add_library(feuerbird-libos-fs
    STATIC
    SOURCES fs/fs.c
    INCLUDES 
        ${CMAKE_CURRENT_SOURCE_DIR}
        ${CMAKE_SOURCE_DIR}/include
    DEPENDENCIES feuerbird-userland feuerbird-protocols
)

# File operations
feuerbird_add_library(feuerbird-libos-file
    STATIC
    SOURCES fs/file.c
    INCLUDES 
        ${CMAKE_CURRENT_SOURCE_DIR}
        ${CMAKE_SOURCE_DIR}/include
    DEPENDENCIES feuerbird-libos-fs
)

# POSIX compatibility layer
feuerbird_add_library(feuerbird-libos-posix
    STATIC
    SOURCES posix/posix.c
    INCLUDES 
        ${CMAKE_CURRENT_SOURCE_DIR}
        ${CMAKE_SOURCE_DIR}/include
    DEPENDENCIES feuerbird-userland
)

# POSIX 2024 stdio implementation
feuerbird_add_library(feuerbird-libos-posix2024-stdio
    STATIC
    SOURCES posix2024/stdio.c
    INCLUDES 
        ${CMAKE_CURRENT_SOURCE_DIR}
        ${CMAKE_CURRENT_SOURCE_DIR}/posix2024
        ${CMAKE_SOURCE_DIR}/include
        ${CMAKE_SOURCE_DIR}/kernel
    DEPENDENCIES feuerbird-libos-posix
)

# Terminal I/O
feuerbird_add_library(feuerbird-libos-termios
    STATIC
    SOURCES termios.c
    INCLUDES 
        ${CMAKE_CURRENT_SOURCE_DIR}
        ${CMAKE_SOURCE_DIR}/include
    DEPENDENCIES feuerbird-libos-posix
)

# IPC layer
feuerbird_add_library(feuerbird-libos-ipc
    STATIC
    SOURCES ipc.c
    INCLUDES 
        ${CMAKE_CURRENT_SOURCE_DIR}
        ${CMAKE_SOURCE_DIR}/include
    DEPENDENCIES feuerbird-userland feuerbird-protocols
)

# Service management
feuerbird_add_library(feuerbird-libos-service
    STATIC
    SOURCES service.c
    INCLUDES 
        ${CMAKE_CURRENT_SOURCE_DIR}
        ${CMAKE_SOURCE_DIR}/include
    DEPENDENCIES feuerbird-libos-ipc
)

# Capability management
feuerbird_add_library(feuerbird-libos-cap
    STATIC
    SOURCES cap.c
    INCLUDES 
        ${CMAKE_CURRENT_SOURCE_DIR}
        ${CMAKE_SOURCE_DIR}/include
    DEPENDENCIES feuerbird-userland
)

# Message router
feuerbird_add_library(feuerbird-libos-msg-router
    STATIC
    SOURCES msg_router.c
    INCLUDES 
        ${CMAKE_CURRENT_SOURCE_DIR}
        ${CMAKE_SOURCE_DIR}/include
    DEPENDENCIES feuerbird-libos-ipc
)

# Resource accounting
feuerbird_add_library(feuerbird-libos-resource-account
    STATIC
    SOURCES resource_account.c
    INCLUDES 
        ${CMAKE_CURRENT_SOURCE_DIR}
        ${CMAKE_SOURCE_DIR}/include
    DEPENDENCIES feuerbird-libos-service
)

# Service registration
feuerbird_add_library(feuerbird-libos-registration
    STATIC
    SOURCES registration.c
    INCLUDES 
        ${CMAKE_CURRENT_SOURCE_DIR}
        ${CMAKE_SOURCE_DIR}/include
    DEPENDENCIES feuerbird-libos-service
)

# Affine runtime
feuerbird_add_library(feuerbird-libos-affine-runtime
    STATIC
    SOURCES affine_runtime.c
    INCLUDES
        ${CMAKE_CURRENT_SOURCE_DIR}
        ${CMAKE_SOURCE_DIR}/include
    DEPENDENCIES feuerbird-architecture
)

# Driver spawn and connection support
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/driver.c")
    feuerbird_add_library(feuerbird-libos-driver
        STATIC
        SOURCES driver.c
        INCLUDES
            ${CMAKE_CURRENT_SOURCE_DIR}
            ${CMAKE_SOURCE_DIR}/include
        DEPENDENCIES feuerbird-userland feuerbird-libos-ipc
    )
endif()

# ═════════════════════════════════════════════════════════════════════
# LIBOS STUBS
# ═════════════════════════════════════════════════════════════════════

# POSIX stubs - Host-backed syscall implementations for user-space demos
# This library is STANDALONE and does not depend on kernel code
# It only uses system headers, no project includes to avoid conflicts
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/stubs/libposix.c")
    add_library(feuerbird-libos-posix-stubs STATIC
        ${CMAKE_CURRENT_SOURCE_DIR}/stubs/libposix.c
    )
    # Use SYSTEM includes and let it find system headers naturally
    target_include_directories(feuerbird-libos-posix-stubs PRIVATE
        ${CMAKE_CURRENT_SOURCE_DIR}/stubs
    )
    # No project includes - this is standalone host code
endif()

# Bare metal stubs
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/stubs/libbaremetal.c")
    feuerbird_add_library(feuerbird-libos-baremetal-stubs
        STATIC
        SOURCES stubs/libbaremetal.c
        INCLUDES
            ${CMAKE_CURRENT_SOURCE_DIR}/stubs
            ${CMAKE_CURRENT_SOURCE_DIR}
            ${CMAKE_SOURCE_DIR}/include
    )
endif()

# 9P protocol stubs - Host-backed 9P client for user-space
# This library is STANDALONE and uses only system headers
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/stubs/lib9p.c")
    add_library(feuerbird-libos-9p-stubs STATIC
        ${CMAKE_CURRENT_SOURCE_DIR}/stubs/lib9p.c
    )
    target_include_directories(feuerbird-libos-9p-stubs PRIVATE
        ${CMAKE_CURRENT_SOURCE_DIR}/stubs
    )
endif()

# ═════════════════════════════════════════════════════════════════════
# CAP'N PROTO INTEGRATION
# ═════════════════════════════════════════════════════════════════════

if(USE_CAPNP AND EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/capnp")
    # Cap'n Proto helpers
    if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/capnp/capnp_helpers.c")
        feuerbird_add_library(feuerbird-libos-capnp-helpers
            STATIC
            SOURCES capnp/capnp_helpers.c
            INCLUDES
                ${CMAKE_CURRENT_SOURCE_DIR}/capnp
                ${CMAKE_CURRENT_SOURCE_DIR}
                ${CMAKE_SOURCE_DIR}/include
                ${CMAKE_SOURCE_DIR}/proto
            DEPENDENCIES feuerbird-protocols
        )
    endif()

    # Capability wrapper
    if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/capwrap.c")
        feuerbird_add_library(feuerbird-libos-capwrap
            STATIC
            SOURCES capwrap.c
            INCLUDES
                ${CMAKE_CURRENT_SOURCE_DIR}
                ${CMAKE_SOURCE_DIR}/include
            DEPENDENCIES feuerbird-libos-cap
        )

        if(TARGET feuerbird-libos-capnp-helpers)
            target_link_libraries(feuerbird-libos-capwrap PUBLIC feuerbird-libos-capnp-helpers)
        endif()
    endif()

    # Process wrapper
    if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/procwrap.c")
        feuerbird_add_library(feuerbird-libos-procwrap
            STATIC
            SOURCES procwrap.c
            INCLUDES
                ${CMAKE_CURRENT_SOURCE_DIR}
                ${CMAKE_SOURCE_DIR}/include
            DEPENDENCIES feuerbird-libos-service
        )
    endif()

    # IRQ client
    if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/irq_client.c")
        feuerbird_add_library(feuerbird-libos-irq-client
            STATIC
            SOURCES irq_client.c
            INCLUDES
                ${CMAKE_CURRENT_SOURCE_DIR}
                ${CMAKE_SOURCE_DIR}/include
            DEPENDENCIES feuerbird-libos-service
        )
    endif()
endif()

# ═════════════════════════════════════════════════════════════════════
# SCHEDULER COMPONENTS
# ═════════════════════════════════════════════════════════════════════

if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/sched.c")
    feuerbird_add_library(feuerbird-libos-sched
        STATIC
        SOURCES sched.c
        INCLUDES
            ${CMAKE_CURRENT_SOURCE_DIR}
            ${CMAKE_SOURCE_DIR}/include
        DEPENDENCIES feuerbird-libos-service
    )
endif()

if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/sched_helpers.c")
    feuerbird_add_library(feuerbird-libos-sched-helpers
        STATIC
        SOURCES sched_helpers.c
        INCLUDES
            ${CMAKE_CURRENT_SOURCE_DIR}
            ${CMAKE_SOURCE_DIR}/include
        DEPENDENCIES feuerbird-libos-sched
    )
endif()

# ═════════════════════════════════════════════════════════════════════
# LIBOS META-LIBRARY
# ═════════════════════════════════════════════════════════════════════

# Collect all LibOS components
set(LIBOS_CORE_LIBS
    feuerbird-libos-fs
    feuerbird-libos-file
    feuerbird-libos-posix
    feuerbird-libos-posix2024-stdio
    feuerbird-libos-termios
    feuerbird-libos-ipc
    feuerbird-libos-service
    feuerbird-libos-cap
    feuerbird-libos-msg-router
    feuerbird-libos-resource-account
    feuerbird-libos-registration
    feuerbird-libos-affine-runtime
)

# Add driver library if built
if(TARGET feuerbird-libos-driver)
    list(APPEND LIBOS_CORE_LIBS feuerbird-libos-driver)
endif()

# Add stub libraries
set(LIBOS_STUB_LIBS)
if(TARGET feuerbird-libos-posix-stubs)
    list(APPEND LIBOS_STUB_LIBS feuerbird-libos-posix-stubs)
endif()
if(TARGET feuerbird-libos-baremetal-stubs)
    list(APPEND LIBOS_STUB_LIBS feuerbird-libos-baremetal-stubs)
endif()
if(TARGET feuerbird-libos-9p-stubs)
    list(APPEND LIBOS_STUB_LIBS feuerbird-libos-9p-stubs)
endif()

# Add Cap'n Proto components if enabled
set(LIBOS_CAPNP_LIBS)
if(USE_CAPNP)
    if(TARGET feuerbird-libos-capnp-helpers)
        list(APPEND LIBOS_CAPNP_LIBS feuerbird-libos-capnp-helpers)
    endif()
    if(TARGET feuerbird-libos-capwrap)
        list(APPEND LIBOS_CAPNP_LIBS feuerbird-libos-capwrap)
    endif()
    if(TARGET feuerbird-libos-procwrap)
        list(APPEND LIBOS_CAPNP_LIBS feuerbird-libos-procwrap)
    endif()
    if(TARGET feuerbird-libos-irq-client)
        list(APPEND LIBOS_CAPNP_LIBS feuerbird-libos-irq-client)
    endif()
endif()

# Add scheduler components
set(LIBOS_SCHED_LIBS)
if(TARGET feuerbird-libos-sched)
    list(APPEND LIBOS_SCHED_LIBS feuerbird-libos-sched)
endif()
if(TARGET feuerbird-libos-sched-helpers)
    list(APPEND LIBOS_SCHED_LIBS feuerbird-libos-sched-helpers)
endif()

# Create the main LibOS library
feuerbird_add_library(feuerbird-libos
    INTERFACE
    DEPENDENCIES
        ${LIBOS_CORE_LIBS}
        ${LIBOS_STUB_LIBS}
        ${LIBOS_CAPNP_LIBS}
        ${LIBOS_SCHED_LIBS}
        feuerbird-userland
        feuerbird-architecture
    INCLUDES
        ${CMAKE_CURRENT_SOURCE_DIR}
        ${CMAKE_CURRENT_SOURCE_DIR}/stubs
        ${CMAKE_CURRENT_SOURCE_DIR}/capnp
        ${CMAKE_SOURCE_DIR}/include
)

# Legacy alias for backward compatibility
add_library(libos ALIAS feuerbird-libos)

# ═════════════════════════════════════════════════════════════════════
# HOSTED LIBOS (for user-space demos running on host OS)
# ═════════════════════════════════════════════════════════════════════

# This variant uses host syscalls instead of kernel-internal functions.
# Suitable for demos and tests that run on Linux/macOS development hosts.
if(TARGET feuerbird-libos-posix-stubs)
    add_library(feuerbird-libos-hosted INTERFACE)
    target_link_libraries(feuerbird-libos-hosted INTERFACE
        feuerbird-libos-posix-stubs
    )
    # Only include stubs directory, not project includes
    target_include_directories(feuerbird-libos-hosted INTERFACE
        ${CMAKE_CURRENT_SOURCE_DIR}/stubs
    )

    # Alias for convenience
    add_library(libos-hosted ALIAS feuerbird-libos-hosted)
    message(STATUS "  - Hosted (user-space) variant: ✓")
endif()

# ═════════════════════════════════════════════════════════════════════
# EXPORTS
# ═════════════════════════════════════════════════════════════════════

set(FEUERBIRD_EXOKERNEL_LIBOS_TARGETS
    feuerbird-libos
    ${LIBOS_CORE_LIBS}
    ${LIBOS_STUB_LIBS}
    ${LIBOS_CAPNP_LIBS}
    ${LIBOS_SCHED_LIBS}
    PARENT_SCOPE
)

message(STATUS "LibOS zone configured:")
message(STATUS "  - Core services: ✓")
message(STATUS "  - POSIX layer: ✓")
message(STATUS "  - POSIX 2024 stdio: ✓")
message(STATUS "  - File system: ✓")
message(STATUS "  - IPC layer: ✓")
if(LIBOS_STUB_LIBS)
    message(STATUS "  - API stubs: ✓")
endif()
if(USE_CAPNP AND LIBOS_CAPNP_LIBS)
    message(STATUS "  - Cap'n Proto: ✓")
endif()
if(LIBOS_SCHED_LIBS)
    message(STATUS "  - Scheduler: ✓")
endif()
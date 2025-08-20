# libos/CMakeLists.txt - Library Operating System

# ═════════════════════════════════════════════════════════════════════
# CORE LIBOS SERVICES
# ═════════════════════════════════════════════════════════════════════

# File system service
exov6_add_library(exov6-libos-fs
    STATIC
    SOURCES fs.c
    INCLUDES 
        ${CMAKE_CURRENT_SOURCE_DIR}
        ${CMAKE_SOURCE_DIR}/include
    DEPENDENCIES exov6-userland exov6-protocols
)

# File operations
exov6_add_library(exov6-libos-file
    STATIC
    SOURCES file.c
    INCLUDES 
        ${CMAKE_CURRENT_SOURCE_DIR}
        ${CMAKE_SOURCE_DIR}/include
    DEPENDENCIES exov6-libos-fs
)

# POSIX compatibility layer
exov6_add_library(exov6-libos-posix
    STATIC
    SOURCES posix.c
    INCLUDES 
        ${CMAKE_CURRENT_SOURCE_DIR}
        ${CMAKE_SOURCE_DIR}/include
    DEPENDENCIES exov6-userland
)

# Terminal I/O
exov6_add_library(exov6-libos-termios
    STATIC
    SOURCES termios.c
    INCLUDES 
        ${CMAKE_CURRENT_SOURCE_DIR}
        ${CMAKE_SOURCE_DIR}/include
    DEPENDENCIES exov6-libos-posix
)

# IPC layer
exov6_add_library(exov6-libos-ipc
    STATIC
    SOURCES ipc.c
    INCLUDES 
        ${CMAKE_CURRENT_SOURCE_DIR}
        ${CMAKE_SOURCE_DIR}/include
    DEPENDENCIES exov6-userland exov6-protocols
)

# Service management
exov6_add_library(exov6-libos-service
    STATIC
    SOURCES service.c
    INCLUDES 
        ${CMAKE_CURRENT_SOURCE_DIR}
        ${CMAKE_SOURCE_DIR}/include
    DEPENDENCIES exov6-libos-ipc
)

# Capability management
exov6_add_library(exov6-libos-cap
    STATIC
    SOURCES cap.c
    INCLUDES 
        ${CMAKE_CURRENT_SOURCE_DIR}
        ${CMAKE_SOURCE_DIR}/include
    DEPENDENCIES exov6-userland
)

# Message router
exov6_add_library(exov6-libos-msg-router
    STATIC
    SOURCES msg_router.c
    INCLUDES 
        ${CMAKE_CURRENT_SOURCE_DIR}
        ${CMAKE_SOURCE_DIR}/include
    DEPENDENCIES exov6-libos-ipc
)

# Resource accounting
exov6_add_library(exov6-libos-resource-account
    STATIC
    SOURCES resource_account.c
    INCLUDES 
        ${CMAKE_CURRENT_SOURCE_DIR}
        ${CMAKE_SOURCE_DIR}/include
    DEPENDENCIES exov6-libos-service
)

# Service registration
exov6_add_library(exov6-libos-registration
    STATIC
    SOURCES registration.c
    INCLUDES 
        ${CMAKE_CURRENT_SOURCE_DIR}
        ${CMAKE_SOURCE_DIR}/include
    DEPENDENCIES exov6-libos-service
)

# Affine runtime
exov6_add_library(exov6-libos-affine-runtime
    STATIC
    SOURCES affine_runtime.c
    INCLUDES 
        ${CMAKE_CURRENT_SOURCE_DIR}
        ${CMAKE_SOURCE_DIR}/include
    DEPENDENCIES exov6-architecture
)

# ═════════════════════════════════════════════════════════════════════
# LIBOS STUBS
# ═════════════════════════════════════════════════════════════════════

# POSIX stubs
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/stubs/libposix.c")
    exov6_add_library(exov6-libos-posix-stubs
        STATIC
        SOURCES stubs/libposix.c
        INCLUDES 
            ${CMAKE_CURRENT_SOURCE_DIR}/stubs
            ${CMAKE_CURRENT_SOURCE_DIR}
            ${CMAKE_SOURCE_DIR}/include
        DEPENDENCIES exov6-libos-posix
    )
endif()

# Bare metal stubs
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/stubs/libbaremetal.c")
    exov6_add_library(exov6-libos-baremetal-stubs
        STATIC
        SOURCES stubs/libbaremetal.c
        INCLUDES 
            ${CMAKE_CURRENT_SOURCE_DIR}/stubs
            ${CMAKE_CURRENT_SOURCE_DIR}
            ${CMAKE_SOURCE_DIR}/include
    )
endif()

# 9P protocol stubs
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/stubs/lib9p.c")
    exov6_add_library(exov6-libos-9p-stubs
        STATIC
        SOURCES stubs/lib9p.c
        INCLUDES 
            ${CMAKE_CURRENT_SOURCE_DIR}/stubs
            ${CMAKE_CURRENT_SOURCE_DIR}
            ${CMAKE_SOURCE_DIR}/include
    )
endif()

# ═════════════════════════════════════════════════════════════════════
# CAP'N PROTO INTEGRATION
# ═════════════════════════════════════════════════════════════════════

if(USE_CAPNP AND EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/capnp")
    # Cap'n Proto helpers
    if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/capnp/capnp_helpers.c")
        exov6_add_library(exov6-libos-capnp-helpers
            STATIC
            SOURCES capnp/capnp_helpers.c
            INCLUDES 
                ${CMAKE_CURRENT_SOURCE_DIR}/capnp
                ${CMAKE_CURRENT_SOURCE_DIR}
                ${CMAKE_SOURCE_DIR}/include
                ${CMAKE_SOURCE_DIR}/proto
            DEPENDENCIES exov6-protocols
        )
    endif()
    
    # Capability wrapper
    if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/capwrap.c")
        exov6_add_library(exov6-libos-capwrap
            STATIC
            SOURCES capwrap.c
            INCLUDES 
                ${CMAKE_CURRENT_SOURCE_DIR}
                ${CMAKE_SOURCE_DIR}/include
            DEPENDENCIES exov6-libos-cap
        )
        
        if(TARGET exov6-libos-capnp-helpers)
            target_link_libraries(exov6-libos-capwrap PUBLIC exov6-libos-capnp-helpers)
        endif()
    endif()
    
    # Process wrapper
    if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/procwrap.c")
        exov6_add_library(exov6-libos-procwrap
            STATIC
            SOURCES procwrap.c
            INCLUDES 
                ${CMAKE_CURRENT_SOURCE_DIR}
                ${CMAKE_SOURCE_DIR}/include
            DEPENDENCIES exov6-libos-service
        )
    endif()
    
    # IRQ client
    if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/irq_client.c")
        exov6_add_library(exov6-libos-irq-client
            STATIC
            SOURCES irq_client.c
            INCLUDES 
                ${CMAKE_CURRENT_SOURCE_DIR}
                ${CMAKE_SOURCE_DIR}/include
            DEPENDENCIES exov6-libos-service
        )
    endif()
endif()

# ═════════════════════════════════════════════════════════════════════
# SCHEDULER COMPONENTS
# ═════════════════════════════════════════════════════════════════════

if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/sched.c")
    exov6_add_library(exov6-libos-sched
        STATIC
        SOURCES sched.c
        INCLUDES 
            ${CMAKE_CURRENT_SOURCE_DIR}
            ${CMAKE_SOURCE_DIR}/include
        DEPENDENCIES exov6-libos-service
    )
endif()

if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/sched_helpers.c")
    exov6_add_library(exov6-libos-sched-helpers
        STATIC
        SOURCES sched_helpers.c
        INCLUDES 
            ${CMAKE_CURRENT_SOURCE_DIR}
            ${CMAKE_SOURCE_DIR}/include
        DEPENDENCIES exov6-libos-sched
    )
endif()

# ═════════════════════════════════════════════════════════════════════
# LIBOS META-LIBRARY
# ═════════════════════════════════════════════════════════════════════

# Collect all LibOS components
set(LIBOS_CORE_LIBS
    exov6-libos-fs
    exov6-libos-file
    exov6-libos-posix
    exov6-libos-termios
    exov6-libos-ipc
    exov6-libos-service
    exov6-libos-cap
    exov6-libos-msg-router
    exov6-libos-resource-account
    exov6-libos-registration
    exov6-libos-affine-runtime
)

# Add stub libraries
set(LIBOS_STUB_LIBS)
if(TARGET exov6-libos-posix-stubs)
    list(APPEND LIBOS_STUB_LIBS exov6-libos-posix-stubs)
endif()
if(TARGET exov6-libos-baremetal-stubs)
    list(APPEND LIBOS_STUB_LIBS exov6-libos-baremetal-stubs)
endif()
if(TARGET exov6-libos-9p-stubs)
    list(APPEND LIBOS_STUB_LIBS exov6-libos-9p-stubs)
endif()

# Add Cap'n Proto components if enabled
set(LIBOS_CAPNP_LIBS)
if(USE_CAPNP)
    if(TARGET exov6-libos-capnp-helpers)
        list(APPEND LIBOS_CAPNP_LIBS exov6-libos-capnp-helpers)
    endif()
    if(TARGET exov6-libos-capwrap)
        list(APPEND LIBOS_CAPNP_LIBS exov6-libos-capwrap)
    endif()
    if(TARGET exov6-libos-procwrap)
        list(APPEND LIBOS_CAPNP_LIBS exov6-libos-procwrap)
    endif()
    if(TARGET exov6-libos-irq-client)
        list(APPEND LIBOS_CAPNP_LIBS exov6-libos-irq-client)
    endif()
endif()

# Add scheduler components
set(LIBOS_SCHED_LIBS)
if(TARGET exov6-libos-sched)
    list(APPEND LIBOS_SCHED_LIBS exov6-libos-sched)
endif()
if(TARGET exov6-libos-sched-helpers)
    list(APPEND LIBOS_SCHED_LIBS exov6-libos-sched-helpers)
endif()

# Create the main LibOS library
exov6_add_library(exov6-libos
    INTERFACE
    DEPENDENCIES 
        ${LIBOS_CORE_LIBS}
        ${LIBOS_STUB_LIBS}
        ${LIBOS_CAPNP_LIBS}
        ${LIBOS_SCHED_LIBS}
        exov6-userland
        exov6-architecture
    INCLUDES 
        ${CMAKE_CURRENT_SOURCE_DIR}
        ${CMAKE_CURRENT_SOURCE_DIR}/stubs
        ${CMAKE_CURRENT_SOURCE_DIR}/capnp
        ${CMAKE_SOURCE_DIR}/include
)

# Legacy alias for backward compatibility
add_library(libos ALIAS exov6-libos)

# ═════════════════════════════════════════════════════════════════════
# EXPORTS
# ═════════════════════════════════════════════════════════════════════

set(EXOV6_LIBOS_TARGETS
    exov6-libos
    ${LIBOS_CORE_LIBS}
    ${LIBOS_STUB_LIBS}
    ${LIBOS_CAPNP_LIBS}
    ${LIBOS_SCHED_LIBS}
    PARENT_SCOPE
)

message(STATUS "LibOS zone configured:")
message(STATUS "  - Core services: ✓")
message(STATUS "  - POSIX layer: ✓")
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
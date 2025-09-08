# libos/CMakeLists.txt - Library Operating System

# ═════════════════════════════════════════════════════════════════════
# CORE LIBOS SERVICES
# ═════════════════════════════════════════════════════════════════════

# File system service
phoenix_add_library(phoenix-libos-fs
    STATIC
    SOURCES fs/fs.c
    INCLUDES 
        ${CMAKE_CURRENT_SOURCE_DIR}
        ${CMAKE_SOURCE_DIR}/include
    DEPENDENCIES phoenix-userland phoenix-protocols
)

# File operations
phoenix_add_library(phoenix-libos-file
    STATIC
    SOURCES fs/file.c
    INCLUDES 
        ${CMAKE_CURRENT_SOURCE_DIR}
        ${CMAKE_SOURCE_DIR}/include
    DEPENDENCIES phoenix-libos-fs
)

# POSIX compatibility layer
phoenix_add_library(phoenix-libos-posix
    STATIC
    SOURCES posix/posix.c
    INCLUDES 
        ${CMAKE_CURRENT_SOURCE_DIR}
        ${CMAKE_SOURCE_DIR}/include
    DEPENDENCIES phoenix-userland
)

# Terminal I/O
phoenix_add_library(phoenix-libos-termios
    STATIC
    SOURCES termios.c
    INCLUDES 
        ${CMAKE_CURRENT_SOURCE_DIR}
        ${CMAKE_SOURCE_DIR}/include
    DEPENDENCIES phoenix-libos-posix
)

# IPC layer
phoenix_add_library(phoenix-libos-ipc
    STATIC
    SOURCES ipc.c
    INCLUDES 
        ${CMAKE_CURRENT_SOURCE_DIR}
        ${CMAKE_SOURCE_DIR}/include
    DEPENDENCIES phoenix-userland phoenix-protocols
)

# Service management
phoenix_add_library(phoenix-libos-service
    STATIC
    SOURCES service.c
    INCLUDES 
        ${CMAKE_CURRENT_SOURCE_DIR}
        ${CMAKE_SOURCE_DIR}/include
    DEPENDENCIES phoenix-libos-ipc
)

# Capability management
phoenix_add_library(phoenix-libos-cap
    STATIC
    SOURCES cap.c
    INCLUDES 
        ${CMAKE_CURRENT_SOURCE_DIR}
        ${CMAKE_SOURCE_DIR}/include
    DEPENDENCIES phoenix-userland
)

# Message router
phoenix_add_library(phoenix-libos-msg-router
    STATIC
    SOURCES msg_router.c
    INCLUDES 
        ${CMAKE_CURRENT_SOURCE_DIR}
        ${CMAKE_SOURCE_DIR}/include
    DEPENDENCIES phoenix-libos-ipc
)

# Resource accounting
phoenix_add_library(phoenix-libos-resource-account
    STATIC
    SOURCES resource_account.c
    INCLUDES 
        ${CMAKE_CURRENT_SOURCE_DIR}
        ${CMAKE_SOURCE_DIR}/include
    DEPENDENCIES phoenix-libos-service
)

# Service registration
phoenix_add_library(phoenix-libos-registration
    STATIC
    SOURCES registration.c
    INCLUDES 
        ${CMAKE_CURRENT_SOURCE_DIR}
        ${CMAKE_SOURCE_DIR}/include
    DEPENDENCIES phoenix-libos-service
)

# Affine runtime
phoenix_add_library(phoenix-libos-affine-runtime
    STATIC
    SOURCES affine_runtime.c
    INCLUDES 
        ${CMAKE_CURRENT_SOURCE_DIR}
        ${CMAKE_SOURCE_DIR}/include
    DEPENDENCIES phoenix-architecture
)

# ═════════════════════════════════════════════════════════════════════
# LIBOS STUBS
# ═════════════════════════════════════════════════════════════════════

# POSIX stubs
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/stubs/libposix.c")
    phoenix_add_library(phoenix-libos-posix-stubs
        STATIC
        SOURCES stubs/libposix.c
        INCLUDES 
            ${CMAKE_CURRENT_SOURCE_DIR}/stubs
            ${CMAKE_CURRENT_SOURCE_DIR}
            ${CMAKE_SOURCE_DIR}/include
        DEPENDENCIES phoenix-libos-posix
    )
endif()

# Bare metal stubs
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/stubs/libbaremetal.c")
    phoenix_add_library(phoenix-libos-baremetal-stubs
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
    phoenix_add_library(phoenix-libos-9p-stubs
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
        phoenix_add_library(phoenix-libos-capnp-helpers
            STATIC
            SOURCES capnp/capnp_helpers.c
            INCLUDES 
                ${CMAKE_CURRENT_SOURCE_DIR}/capnp
                ${CMAKE_CURRENT_SOURCE_DIR}
                ${CMAKE_SOURCE_DIR}/include
                ${CMAKE_SOURCE_DIR}/proto
            DEPENDENCIES phoenix-protocols
        )
    endif()
    
    # Capability wrapper
    if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/capwrap.c")
        phoenix_add_library(phoenix-libos-capwrap
            STATIC
            SOURCES capwrap.c
            INCLUDES 
                ${CMAKE_CURRENT_SOURCE_DIR}
                ${CMAKE_SOURCE_DIR}/include
            DEPENDENCIES phoenix-libos-cap
        )
        
        if(TARGET phoenix-libos-capnp-helpers)
            target_link_libraries(phoenix-libos-capwrap PUBLIC phoenix-libos-capnp-helpers)
        endif()
    endif()
    
    # Process wrapper
    if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/procwrap.c")
        phoenix_add_library(phoenix-libos-procwrap
            STATIC
            SOURCES procwrap.c
            INCLUDES 
                ${CMAKE_CURRENT_SOURCE_DIR}
                ${CMAKE_SOURCE_DIR}/include
            DEPENDENCIES phoenix-libos-service
        )
    endif()
    
    # IRQ client
    if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/irq_client.c")
        phoenix_add_library(phoenix-libos-irq-client
            STATIC
            SOURCES irq_client.c
            INCLUDES 
                ${CMAKE_CURRENT_SOURCE_DIR}
                ${CMAKE_SOURCE_DIR}/include
            DEPENDENCIES phoenix-libos-service
        )
    endif()
endif()

# ═════════════════════════════════════════════════════════════════════
# SCHEDULER COMPONENTS
# ═════════════════════════════════════════════════════════════════════

if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/sched.c")
    phoenix_add_library(phoenix-libos-sched
        STATIC
        SOURCES sched.c
        INCLUDES 
            ${CMAKE_CURRENT_SOURCE_DIR}
            ${CMAKE_SOURCE_DIR}/include
        DEPENDENCIES phoenix-libos-service
    )
endif()

if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/sched_helpers.c")
    phoenix_add_library(phoenix-libos-sched-helpers
        STATIC
        SOURCES sched_helpers.c
        INCLUDES 
            ${CMAKE_CURRENT_SOURCE_DIR}
            ${CMAKE_SOURCE_DIR}/include
        DEPENDENCIES phoenix-libos-sched
    )
endif()

# ═════════════════════════════════════════════════════════════════════
# LIBOS META-LIBRARY
# ═════════════════════════════════════════════════════════════════════

# Collect all LibOS components
set(LIBOS_CORE_LIBS
    phoenix-libos-fs
    phoenix-libos-file
    phoenix-libos-posix
    phoenix-libos-termios
    phoenix-libos-ipc
    phoenix-libos-service
    phoenix-libos-cap
    phoenix-libos-msg-router
    phoenix-libos-resource-account
    phoenix-libos-registration
    phoenix-libos-affine-runtime
)

# Add stub libraries
set(LIBOS_STUB_LIBS)
if(TARGET phoenix-libos-posix-stubs)
    list(APPEND LIBOS_STUB_LIBS phoenix-libos-posix-stubs)
endif()
if(TARGET phoenix-libos-baremetal-stubs)
    list(APPEND LIBOS_STUB_LIBS phoenix-libos-baremetal-stubs)
endif()
if(TARGET phoenix-libos-9p-stubs)
    list(APPEND LIBOS_STUB_LIBS phoenix-libos-9p-stubs)
endif()

# Add Cap'n Proto components if enabled
set(LIBOS_CAPNP_LIBS)
if(USE_CAPNP)
    if(TARGET phoenix-libos-capnp-helpers)
        list(APPEND LIBOS_CAPNP_LIBS phoenix-libos-capnp-helpers)
    endif()
    if(TARGET phoenix-libos-capwrap)
        list(APPEND LIBOS_CAPNP_LIBS phoenix-libos-capwrap)
    endif()
    if(TARGET phoenix-libos-procwrap)
        list(APPEND LIBOS_CAPNP_LIBS phoenix-libos-procwrap)
    endif()
    if(TARGET phoenix-libos-irq-client)
        list(APPEND LIBOS_CAPNP_LIBS phoenix-libos-irq-client)
    endif()
endif()

# Add scheduler components
set(LIBOS_SCHED_LIBS)
if(TARGET phoenix-libos-sched)
    list(APPEND LIBOS_SCHED_LIBS phoenix-libos-sched)
endif()
if(TARGET phoenix-libos-sched-helpers)
    list(APPEND LIBOS_SCHED_LIBS phoenix-libos-sched-helpers)
endif()

# Create the main LibOS library
phoenix_add_library(phoenix-libos
    INTERFACE
    DEPENDENCIES 
        ${LIBOS_CORE_LIBS}
        ${LIBOS_STUB_LIBS}
        ${LIBOS_CAPNP_LIBS}
        ${LIBOS_SCHED_LIBS}
        phoenix-userland
        phoenix-architecture
    INCLUDES 
        ${CMAKE_CURRENT_SOURCE_DIR}
        ${CMAKE_CURRENT_SOURCE_DIR}/stubs
        ${CMAKE_CURRENT_SOURCE_DIR}/capnp
        ${CMAKE_SOURCE_DIR}/include
)

# Legacy alias for backward compatibility
add_library(libos ALIAS phoenix-libos)

# ═════════════════════════════════════════════════════════════════════
# EXPORTS
# ═════════════════════════════════════════════════════════════════════

set(EXOV6_LIBOS_TARGETS
    phoenix-libos
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
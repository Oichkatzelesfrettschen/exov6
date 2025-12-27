# user/CMakeLists.txt - Userland Core Libraries and Applications

# ═════════════════════════════════════════════════════════════════════
# CORE USER LIBRARIES
# ═════════════════════════════════════════════════════════════════════

# User library (ulib) - Core user space functionality
feuerbird_add_library(feuerbird-ulib
    STATIC
    SOURCES ulib.c usys.S
    INCLUDES
        ${CMAKE_CURRENT_SOURCE_DIR}
        ${CMAKE_SOURCE_DIR}/include
    DEPENDENCIES feuerbird-protocols
)

# User memory allocator (umalloc)
feuerbird_add_library(feuerbird-umalloc
    STATIC
    SOURCES umalloc.c
    INCLUDES
        ${CMAKE_CURRENT_SOURCE_DIR}
        ${CMAKE_SOURCE_DIR}/include
    DEPENDENCIES feuerbird-ulib
)

# Printf implementation
feuerbird_add_library(feuerbird-printf
    STATIC
    SOURCES printf.c
    INCLUDES
        ${CMAKE_CURRENT_SOURCE_DIR}
        ${CMAKE_SOURCE_DIR}/include
    DEPENDENCIES feuerbird-ulib
)

# Capability library (caplib)
feuerbird_add_library(feuerbird-caplib
    STATIC
    SOURCES caplib.c
    INCLUDES
        ${CMAKE_CURRENT_SOURCE_DIR}
        ${CMAKE_SOURCE_DIR}/include
    DEPENDENCIES feuerbird-ulib feuerbird-protocols
)

# Channel library (chan)
feuerbird_add_library(feuerbird-chan
    STATIC
    SOURCES
        chan.c
        unified_chan.c
    INCLUDES
        ${CMAKE_CURRENT_SOURCE_DIR}
        ${CMAKE_SOURCE_DIR}/include
    DEPENDENCIES feuerbird-caplib feuerbird-protocols
)

# Door library (door)
feuerbird_add_library(feuerbird-door
    STATIC
    SOURCES door.c
    INCLUDES
        ${CMAKE_CURRENT_SOURCE_DIR}
        ${CMAKE_SOURCE_DIR}/include
    DEPENDENCIES feuerbird-caplib feuerbird-protocols
)

# Endpoint library (user-space IPC stubs)
feuerbird_add_library(feuerbird-endpoint
    STATIC
    SOURCES endpoint.c
    INCLUDES
        ${CMAKE_CURRENT_SOURCE_DIR}
        ${CMAKE_SOURCE_DIR}/include
    DEPENDENCIES feuerbird-ulib
)

# Math core library
feuerbird_add_library(feuerbird-math-core
    STATIC
    SOURCES math_core.c
    INCLUDES
        ${CMAKE_CURRENT_SOURCE_DIR}
        ${CMAKE_SOURCE_DIR}/include
    DEPENDENCIES feuerbird-architecture
)

# ═════════════════════════════════════════════════════════════════════
# USER-LEVEL LIBOS COMPONENTS
# ═════════════════════════════════════════════════════════════════════

if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/libos")
    # User-level scheduler
    if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/libos/sched.c")
        feuerbird_add_library(feuerbird-user-sched
            STATIC
            SOURCES libos/sched.c
            INCLUDES
                ${CMAKE_CURRENT_SOURCE_DIR}/libos
                ${CMAKE_CURRENT_SOURCE_DIR}
                ${CMAKE_SOURCE_DIR}/include
            DEPENDENCIES feuerbird-caplib feuerbird-chan
        )
    endif()

    # Additional user-level libos components
    file(GLOB USER_LIBOS_SOURCES libos/*.c)
    if(USER_LIBOS_SOURCES)
        # Filter out sched.c if it was handled separately
        list(REMOVE_ITEM USER_LIBOS_SOURCES "${CMAKE_CURRENT_SOURCE_DIR}/libos/sched.c")

        if(USER_LIBOS_SOURCES)
            feuerbird_add_library(feuerbird-user-libos-extra
                STATIC
                SOURCES ${USER_LIBOS_SOURCES}
                INCLUDES
                    ${CMAKE_CURRENT_SOURCE_DIR}/libos
                    ${CMAKE_CURRENT_SOURCE_DIR}
                    ${CMAKE_SOURCE_DIR}/include
                DEPENDENCIES feuerbird-caplib feuerbird-chan
            )
        endif()
    endif()
endif()

# ═════════════════════════════════════════════════════════════════════
# USER APPLICATIONS
# ═════════════════════════════════════════════════════════════════════

# Core user applications
#
# The microcontroller-specific "blink" demo relies on MCU headers
# that are only available when the MCU build option is enabled.  Building it
# unconditionally causes missing-header failures on hosted builds.  We therefore
# keep it separate and inject it only when the MCU option is active.
set(USER_APPS
    cat
    echo
    grep
    init
    kill
    ln
    ls
    mkdir
    rm
    sh
    wc
    zombie
)

# Conditionally include MCU demos
if(MCU)
    list(INSERT USER_APPS 0 blink)
endif()

# Build each user application
foreach(app ${USER_APPS})
    if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/${app}.c")
        feuerbird_add_executable(user-${app}
            SOURCES ${app}.c
            INCLUDES
                ${CMAKE_CURRENT_SOURCE_DIR}
                ${CMAKE_SOURCE_DIR}/include
            DEPENDENCIES
                feuerbird-ulib
                feuerbird-umalloc
                feuerbird-printf
                feuerbird-caplib
        )

        # Set output name without prefix (the framework adds feuerbird- prefix)
        set_target_properties(user-${app} PROPERTIES
            OUTPUT_NAME ${app}
            PREFIX ""
        )
    else()
        message(STATUS "Skipping ${app} - source file not found")
    endif()
endforeach()

# Special applications with additional dependencies
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/fileserver.c")
    feuerbird_add_executable(user-fileserver
        SOURCES fileserver.c
        INCLUDES
            ${CMAKE_CURRENT_SOURCE_DIR}
            ${CMAKE_SOURCE_DIR}/include
        DEPENDENCIES
            feuerbird-ulib
            feuerbird-umalloc
            feuerbird-printf
            feuerbird-caplib
            feuerbird-chan
            feuerbird-door
            feuerbird-endpoint
    )
    set_target_properties(user-fileserver PROPERTIES
        OUTPUT_NAME fileserver
        PREFIX ""
    )
else()
    message(STATUS "Skipping fileserver - source file not found")
endif()

# Test applications
set(TEST_APPS
    usertests
    forktest
    stressfs
)

foreach(test_app ${TEST_APPS})
    if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/${test_app}.c")
        feuerbird_add_executable(user-${test_app}
            SOURCES ${test_app}.c
            INCLUDES
                ${CMAKE_CURRENT_SOURCE_DIR}
                ${CMAKE_SOURCE_DIR}/include
            DEPENDENCIES
                feuerbird-ulib
                feuerbird-umalloc
                feuerbird-printf
                feuerbird-caplib
        )

        set_target_properties(user-${test_app} PROPERTIES
            OUTPUT_NAME ${test_app}
            PREFIX ""
        )
    else()
        message(STATUS "Skipping ${test_app} - source file not found")
    endif()
endforeach()

# ═════════════════════════════════════════════════════════════════════
# USERLAND META-LIBRARY
# ═════════════════════════════════════════════════════════════════════

# Create meta-library that includes all core userland components
set(USERLAND_LIBS
    feuerbird-ulib
    feuerbird-umalloc
    feuerbird-printf
    feuerbird-caplib
    feuerbird-chan
    feuerbird-door
    feuerbird-endpoint
    feuerbird-math-core
)

# Add user-level libos components if they exist
if(TARGET feuerbird-user-sched)
    list(APPEND USERLAND_LIBS feuerbird-user-sched)
endif()
if(TARGET feuerbird-user-libos-extra)
    list(APPEND USERLAND_LIBS feuerbird-user-libos-extra)
endif()

feuerbird_add_library(feuerbird-userland
    INTERFACE
    DEPENDENCIES ${USERLAND_LIBS}
    INCLUDES
        ${CMAKE_CURRENT_SOURCE_DIR}
        ${CMAKE_SOURCE_DIR}/include
)

# ═════════════════════════════════════════════════════════════════════
# EXPORTS
# ═════════════════════════════════════════════════════════════════════

set(FEUERBIRD_EXOKERNEL_USERLAND_TARGETS
    feuerbird-userland
    ${USERLAND_LIBS}
    PARENT_SCOPE
)

message(STATUS "Userland zone configured:")
message(STATUS "  - Core libraries: ✓")
message(STATUS "  - User applications: ✓")
if(TARGET feuerbird-user-sched)
    message(STATUS "  - User-level scheduler: ✓")
endif()
message(STATUS "  - Test applications: ✓")
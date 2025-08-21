# user/CMakeLists.txt - Userland Core Libraries and Applications

# ═════════════════════════════════════════════════════════════════════
# CORE USER LIBRARIES
# ═════════════════════════════════════════════════════════════════════

# User library (ulib) - Core user space functionality
phoenix_add_library(phoenix-ulib
    STATIC
    SOURCES ulib.c
    INCLUDES 
        ${CMAKE_CURRENT_SOURCE_DIR}
        ${CMAKE_SOURCE_DIR}/include
    DEPENDENCIES phoenix-protocols
)

# User memory allocator (umalloc)
phoenix_add_library(phoenix-umalloc
    STATIC
    SOURCES umalloc.c
    INCLUDES 
        ${CMAKE_CURRENT_SOURCE_DIR}
        ${CMAKE_SOURCE_DIR}/include
    DEPENDENCIES phoenix-ulib
)

# Printf implementation
phoenix_add_library(phoenix-printf
    STATIC
    SOURCES printf.c
    INCLUDES 
        ${CMAKE_CURRENT_SOURCE_DIR}
        ${CMAKE_SOURCE_DIR}/include
    DEPENDENCIES phoenix-ulib
)

# Capability library (caplib)
phoenix_add_library(phoenix-caplib
    STATIC
    SOURCES caplib.c
    INCLUDES 
        ${CMAKE_CURRENT_SOURCE_DIR}
        ${CMAKE_SOURCE_DIR}/include
    DEPENDENCIES phoenix-ulib phoenix-protocols
)

# Channel library (chan)
phoenix_add_library(phoenix-chan
    STATIC
    SOURCES chan.c
    INCLUDES 
        ${CMAKE_CURRENT_SOURCE_DIR}
        ${CMAKE_SOURCE_DIR}/include
    DEPENDENCIES phoenix-caplib phoenix-protocols
)

# Door library (door)
phoenix_add_library(phoenix-door
    STATIC
    SOURCES door.c
    INCLUDES 
        ${CMAKE_CURRENT_SOURCE_DIR}
        ${CMAKE_SOURCE_DIR}/include
    DEPENDENCIES phoenix-caplib phoenix-protocols
)

# Math core library
phoenix_add_library(phoenix-math-core
    STATIC
    SOURCES math_core.c
    INCLUDES 
        ${CMAKE_CURRENT_SOURCE_DIR}
        ${CMAKE_SOURCE_DIR}/include
    DEPENDENCIES phoenix-architecture
)

# ═════════════════════════════════════════════════════════════════════
# USER-LEVEL LIBOS COMPONENTS
# ═════════════════════════════════════════════════════════════════════

if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/libos")
    # User-level scheduler
    if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/libos/sched.c")
        phoenix_add_library(phoenix-user-sched
            STATIC
            SOURCES libos/sched.c
            INCLUDES 
                ${CMAKE_CURRENT_SOURCE_DIR}/libos
                ${CMAKE_CURRENT_SOURCE_DIR}
                ${CMAKE_SOURCE_DIR}/include
            DEPENDENCIES phoenix-caplib phoenix-chan
        )
    endif()
    
    # Additional user-level libos components
    file(GLOB USER_LIBOS_SOURCES libos/*.c)
    if(USER_LIBOS_SOURCES)
        # Filter out sched.c if it was handled separately
        list(REMOVE_ITEM USER_LIBOS_SOURCES "${CMAKE_CURRENT_SOURCE_DIR}/libos/sched.c")
        
        if(USER_LIBOS_SOURCES)
            phoenix_add_library(phoenix-user-libos-extra
                STATIC
                SOURCES ${USER_LIBOS_SOURCES}
                INCLUDES 
                    ${CMAKE_CURRENT_SOURCE_DIR}/libos
                    ${CMAKE_CURRENT_SOURCE_DIR}
                    ${CMAKE_SOURCE_DIR}/include
                DEPENDENCIES phoenix-caplib phoenix-chan
            )
        endif()
    endif()
endif()

# ═════════════════════════════════════════════════════════════════════
# USER APPLICATIONS
# ═════════════════════════════════════════════════════════════════════

# Core user applications
set(USER_APPS
    blink
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

# Build each user application
foreach(app ${USER_APPS})
    if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/${app}.c")
        phoenix_add_executable(user-${app}
            SOURCES ${app}.c
            INCLUDES 
                ${CMAKE_CURRENT_SOURCE_DIR}
                ${CMAKE_SOURCE_DIR}/include
            DEPENDENCIES 
                phoenix-ulib 
                phoenix-umalloc 
                phoenix-printf 
                phoenix-caplib
        )
        
        # Set output name without prefix (the framework adds phoenix- prefix)
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
    phoenix_add_executable(user-fileserver
        SOURCES fileserver.c
        INCLUDES 
            ${CMAKE_CURRENT_SOURCE_DIR}
            ${CMAKE_SOURCE_DIR}/include
        DEPENDENCIES 
            phoenix-ulib 
            phoenix-umalloc 
            phoenix-printf 
            phoenix-caplib
            phoenix-chan
            phoenix-door
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
        phoenix_add_executable(user-${test_app}
            SOURCES ${test_app}.c
            INCLUDES 
                ${CMAKE_CURRENT_SOURCE_DIR}
                ${CMAKE_SOURCE_DIR}/include
            DEPENDENCIES 
                phoenix-ulib 
                phoenix-umalloc 
                phoenix-printf 
                phoenix-caplib
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
    phoenix-ulib
    phoenix-umalloc
    phoenix-printf
    phoenix-caplib
    phoenix-chan
    phoenix-door
    phoenix-math-core
)

# Add user-level libos components if they exist
if(TARGET phoenix-user-sched)
    list(APPEND USERLAND_LIBS phoenix-user-sched)
endif()
if(TARGET phoenix-user-libos-extra)
    list(APPEND USERLAND_LIBS phoenix-user-libos-extra)
endif()

phoenix_add_library(phoenix-userland
    INTERFACE
    DEPENDENCIES ${USERLAND_LIBS}
    INCLUDES 
        ${CMAKE_CURRENT_SOURCE_DIR}
        ${CMAKE_SOURCE_DIR}/include
)

# ═════════════════════════════════════════════════════════════════════
# EXPORTS
# ═════════════════════════════════════════════════════════════════════

set(EXOV6_USERLAND_TARGETS
    phoenix-userland
    ${USERLAND_LIBS}
    PARENT_SCOPE
)

message(STATUS "Userland zone configured:")
message(STATUS "  - Core libraries: ✓")
message(STATUS "  - User applications: ✓")
if(TARGET phoenix-user-sched)
    message(STATUS "  - User-level scheduler: ✓")
endif()
message(STATUS "  - Test applications: ✓")
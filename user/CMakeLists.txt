# user/CMakeLists.txt - Userland Core Libraries and Applications

# ═════════════════════════════════════════════════════════════════════
# CORE USER LIBRARIES
# ═════════════════════════════════════════════════════════════════════

# User library (ulib) - Core user space functionality
exov6_add_library(exov6-ulib
    STATIC
    SOURCES ulib.c
    INCLUDES 
        ${CMAKE_CURRENT_SOURCE_DIR}
        ${CMAKE_SOURCE_DIR}/include
    DEPENDENCIES exov6-protocols
)

# User memory allocator (umalloc)
exov6_add_library(exov6-umalloc
    STATIC
    SOURCES umalloc.c
    INCLUDES 
        ${CMAKE_CURRENT_SOURCE_DIR}
        ${CMAKE_SOURCE_DIR}/include
    DEPENDENCIES exov6-ulib
)

# Printf implementation
exov6_add_library(exov6-printf
    STATIC
    SOURCES printf.c
    INCLUDES 
        ${CMAKE_CURRENT_SOURCE_DIR}
        ${CMAKE_SOURCE_DIR}/include
    DEPENDENCIES exov6-ulib
)

# Capability library (caplib)
exov6_add_library(exov6-caplib
    STATIC
    SOURCES caplib.c
    INCLUDES 
        ${CMAKE_CURRENT_SOURCE_DIR}
        ${CMAKE_SOURCE_DIR}/include
    DEPENDENCIES exov6-ulib exov6-protocols
)

# Channel library (chan)
exov6_add_library(exov6-chan
    STATIC
    SOURCES chan.c
    INCLUDES 
        ${CMAKE_CURRENT_SOURCE_DIR}
        ${CMAKE_SOURCE_DIR}/include
    DEPENDENCIES exov6-caplib exov6-protocols
)

# Door library (door)
exov6_add_library(exov6-door
    STATIC
    SOURCES door.c
    INCLUDES 
        ${CMAKE_CURRENT_SOURCE_DIR}
        ${CMAKE_SOURCE_DIR}/include
    DEPENDENCIES exov6-caplib exov6-protocols
)

# Math core library
exov6_add_library(exov6-math-core
    STATIC
    SOURCES math_core.c
    INCLUDES 
        ${CMAKE_CURRENT_SOURCE_DIR}
        ${CMAKE_SOURCE_DIR}/include
    DEPENDENCIES exov6-architecture
)

# ═════════════════════════════════════════════════════════════════════
# USER-LEVEL LIBOS COMPONENTS
# ═════════════════════════════════════════════════════════════════════

if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/libos")
    # User-level scheduler
    if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/libos/sched.c")
        exov6_add_library(exov6-user-sched
            STATIC
            SOURCES libos/sched.c
            INCLUDES 
                ${CMAKE_CURRENT_SOURCE_DIR}/libos
                ${CMAKE_CURRENT_SOURCE_DIR}
                ${CMAKE_SOURCE_DIR}/include
            DEPENDENCIES exov6-caplib exov6-chan
        )
    endif()
    
    # Additional user-level libos components
    file(GLOB USER_LIBOS_SOURCES libos/*.c)
    if(USER_LIBOS_SOURCES)
        # Filter out sched.c if it was handled separately
        list(REMOVE_ITEM USER_LIBOS_SOURCES "${CMAKE_CURRENT_SOURCE_DIR}/libos/sched.c")
        
        if(USER_LIBOS_SOURCES)
            exov6_add_library(exov6-user-libos-extra
                STATIC
                SOURCES ${USER_LIBOS_SOURCES}
                INCLUDES 
                    ${CMAKE_CURRENT_SOURCE_DIR}/libos
                    ${CMAKE_CURRENT_SOURCE_DIR}
                    ${CMAKE_SOURCE_DIR}/include
                DEPENDENCIES exov6-caplib exov6-chan
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
        exov6_add_executable(user-${app}
            SOURCES ${app}.c
            INCLUDES 
                ${CMAKE_CURRENT_SOURCE_DIR}
                ${CMAKE_SOURCE_DIR}/include
            DEPENDENCIES 
                exov6-ulib 
                exov6-umalloc 
                exov6-printf 
                exov6-caplib
        )
        
        # Set output name without prefix (the framework adds exov6- prefix)
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
    exov6_add_executable(user-fileserver
        SOURCES fileserver.c
        INCLUDES 
            ${CMAKE_CURRENT_SOURCE_DIR}
            ${CMAKE_SOURCE_DIR}/include
        DEPENDENCIES 
            exov6-ulib 
            exov6-umalloc 
            exov6-printf 
            exov6-caplib
            exov6-chan
            exov6-door
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
        exov6_add_executable(user-${test_app}
            SOURCES ${test_app}.c
            INCLUDES 
                ${CMAKE_CURRENT_SOURCE_DIR}
                ${CMAKE_SOURCE_DIR}/include
            DEPENDENCIES 
                exov6-ulib 
                exov6-umalloc 
                exov6-printf 
                exov6-caplib
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
    exov6-ulib
    exov6-umalloc
    exov6-printf
    exov6-caplib
    exov6-chan
    exov6-door
    exov6-math-core
)

# Add user-level libos components if they exist
if(TARGET exov6-user-sched)
    list(APPEND USERLAND_LIBS exov6-user-sched)
endif()
if(TARGET exov6-user-libos-extra)
    list(APPEND USERLAND_LIBS exov6-user-libos-extra)
endif()

exov6_add_library(exov6-userland
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
    exov6-userland
    ${USERLAND_LIBS}
    PARENT_SCOPE
)

message(STATUS "Userland zone configured:")
message(STATUS "  - Core libraries: ✓")
message(STATUS "  - User applications: ✓")
if(TARGET exov6-user-sched)
    message(STATUS "  - User-level scheduler: ✓")
endif()
message(STATUS "  - Test applications: ✓")
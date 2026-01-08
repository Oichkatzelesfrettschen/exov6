# FeuerBirdConfig.cmake - Build Configuration for FeuerBird Exokernel
# Provides helper functions and macros for the build system

# ===========================================================================
# VERSION INFORMATION
# ===========================================================================
set(FEUERBIRD_VERSION_MAJOR 1)
set(FEUERBIRD_VERSION_MINOR 0)
set(FEUERBIRD_VERSION_PATCH 0)
set(FEUERBIRD_VERSION "${FEUERBIRD_VERSION_MAJOR}.${FEUERBIRD_VERSION_MINOR}.${FEUERBIRD_VERSION_PATCH}")

# ===========================================================================
# HELPER FUNCTIONS
# ===========================================================================

# feuerbird_detect_llvm_tools()
# Detects available LLVM toolchain components
function(feuerbird_detect_llvm_tools)
    set(FEUERBIRD_EXOKERNEL_LLVM_TOOLS_AVAILABLE FALSE PARENT_SCOPE)

    # Check for clang
    if(CMAKE_C_COMPILER_ID MATCHES "Clang")
        set(FEUERBIRD_EXOKERNEL_HAS_CLANG TRUE PARENT_SCOPE)

        # Check for LLD linker
        find_program(LLD_EXECUTABLE NAMES ld.lld lld)
        if(LLD_EXECUTABLE)
            set(FEUERBIRD_EXOKERNEL_HAS_LLD TRUE PARENT_SCOPE)
        endif()

        # Check for LLVM AR
        find_program(LLVM_AR_EXECUTABLE NAMES llvm-ar)
        if(LLVM_AR_EXECUTABLE)
            set(FEUERBIRD_EXOKERNEL_HAS_LLVM_AR TRUE PARENT_SCOPE)
        endif()

        # Check for Polly
        find_program(OPT_EXECUTABLE NAMES opt)
        if(OPT_EXECUTABLE)
            execute_process(
                COMMAND ${OPT_EXECUTABLE} --help
                OUTPUT_VARIABLE OPT_HELP
                ERROR_QUIET
            )
            if(OPT_HELP MATCHES "polly")
                set(FEUERBIRD_EXOKERNEL_HAS_POLLY TRUE PARENT_SCOPE)
            endif()
        endif()

        set(FEUERBIRD_EXOKERNEL_LLVM_TOOLS_AVAILABLE TRUE PARENT_SCOPE)
    endif()
endfunction()

# feuerbird_add_library(name [STATIC|SHARED|INTERFACE] sources...)
# Creates a library with FeuerBird standard settings
# INTERFACE libraries are header-only and don't require sources
function(feuerbird_add_library name)
    cmake_parse_arguments(ARG "STATIC;SHARED;INTERFACE" "" "SOURCES;INCLUDES;DEFINITIONS;DEPENDS;DEPENDENCIES" ${ARGN})

    # Determine library type
    if(ARG_INTERFACE)
        set(LIB_TYPE INTERFACE)
    elseif(ARG_STATIC)
        set(LIB_TYPE STATIC)
    elseif(ARG_SHARED)
        set(LIB_TYPE SHARED)
    else()
        set(LIB_TYPE STATIC)
    endif()

    # Create the library
    if(LIB_TYPE STREQUAL "INTERFACE")
        add_library(${name} INTERFACE)
    else()
        add_library(${name} ${LIB_TYPE} ${ARG_SOURCES})
    endif()

    # Handle includes - INTERFACE libraries use INTERFACE visibility
    if(ARG_INCLUDES)
        if(LIB_TYPE STREQUAL "INTERFACE")
            target_include_directories(${name} INTERFACE ${ARG_INCLUDES})
        else()
            target_include_directories(${name} PRIVATE ${ARG_INCLUDES})
        endif()
    endif()

    # Handle definitions
    if(ARG_DEFINITIONS)
        if(LIB_TYPE STREQUAL "INTERFACE")
            target_compile_definitions(${name} INTERFACE ${ARG_DEFINITIONS})
        else()
            target_compile_definitions(${name} PRIVATE ${ARG_DEFINITIONS})
        endif()
    endif()

    # Handle dependencies (both DEPENDS and DEPENDENCIES for flexibility)
    set(ALL_DEPS ${ARG_DEPENDS} ${ARG_DEPENDENCIES})
    if(ALL_DEPS)
        if(LIB_TYPE STREQUAL "INTERFACE")
            target_link_libraries(${name} INTERFACE ${ALL_DEPS})
        else()
            target_link_libraries(${name} PRIVATE ${ALL_DEPS})
        endif()
    endif()

    # Apply standard compile options (only for non-INTERFACE libraries)
    if(NOT LIB_TYPE STREQUAL "INTERFACE")
        target_compile_options(${name} PRIVATE
            -Wall -Wextra -Wpedantic
            $<$<CONFIG:Debug>:-g -O0>
            $<$<CONFIG:Release>:-O2>
            $<$<CONFIG:RelWithDebInfo>:-O2 -g>
        )
    endif()
endfunction()

# feuerbird_add_executable(name sources...)
# Creates an executable with FeuerBird standard settings
function(feuerbird_add_executable name)
    cmake_parse_arguments(ARG "" "" "SOURCES;INCLUDES;DEFINITIONS;DEPENDS;DEPENDENCIES" ${ARGN})

    add_executable(${name} ${ARG_SOURCES})

    if(ARG_INCLUDES)
        target_include_directories(${name} PRIVATE ${ARG_INCLUDES})
    endif()

    if(ARG_DEFINITIONS)
        target_compile_definitions(${name} PRIVATE ${ARG_DEFINITIONS})
    endif()

    # Handle dependencies (both DEPENDS and DEPENDENCIES for flexibility)
    set(ALL_DEPS ${ARG_DEPENDS} ${ARG_DEPENDENCIES})
    if(ALL_DEPS)
        target_link_libraries(${name} PRIVATE ${ALL_DEPS})
    endif()

    # Apply standard compile options
    target_compile_options(${name} PRIVATE
        -Wall -Wextra -Wpedantic
        $<$<CONFIG:Debug>:-g -O0>
        $<$<CONFIG:Release>:-O2>
        $<$<CONFIG:RelWithDebInfo>:-O2 -g>
    )
endfunction()

# generate_config_header()
# Generates the feuerbird_config.h header from config.h.in
function(generate_config_header)
    # Configure the header file
    configure_file(
        "${CMAKE_SOURCE_DIR}/cmake/config.h.in"
        "${CMAKE_BINARY_DIR}/include/feuerbird_config.h"
        @ONLY
    )
endfunction()

# ===========================================================================
# PLATFORM DETECTION
# ===========================================================================

# Detect platform
if(CMAKE_SYSTEM_NAME STREQUAL "Linux")
    set(FEUERBIRD_EXOKERNEL_PLATFORM_LINUX TRUE)
elseif(CMAKE_SYSTEM_NAME STREQUAL "Darwin")
    set(FEUERBIRD_EXOKERNEL_PLATFORM_MACOS TRUE)
elseif(CMAKE_SYSTEM_NAME STREQUAL "Windows")
    set(FEUERBIRD_EXOKERNEL_PLATFORM_WINDOWS TRUE)
endif()

# Detect architecture
if(CMAKE_SYSTEM_PROCESSOR MATCHES "x86_64|AMD64")
    set(FEUERBIRD_EXOKERNEL_ARCH_X86_64 TRUE)
elseif(CMAKE_SYSTEM_PROCESSOR MATCHES "aarch64|ARM64")
    set(FEUERBIRD_EXOKERNEL_ARCH_AARCH64 TRUE)
elseif(CMAKE_SYSTEM_PROCESSOR MATCHES "arm")
    set(FEUERBIRD_EXOKERNEL_ARCH_ARM TRUE)
elseif(CMAKE_SYSTEM_PROCESSOR MATCHES "powerpc|ppc")
    set(FEUERBIRD_EXOKERNEL_ARCH_PPC TRUE)
endif()

# ===========================================================================
# DEFAULT INCLUDE PATHS
# ===========================================================================

set(FEUERBIRD_EXOKERNEL_INCLUDE_DIRS
    ${CMAKE_SOURCE_DIR}/include
    ${CMAKE_SOURCE_DIR}/kernel/include
    ${CMAKE_SOURCE_DIR}/libos
    ${CMAKE_SOURCE_DIR}/proto
    ${CMAKE_BINARY_DIR}/include
)

# ===========================================================================
# LEGACY ALIASES (REMOVED)
# ===========================================================================
# phoenix_* aliases were removed in the feuerbird rename consolidation.
# All CMakeLists.txt files should use feuerbird_add_executable() and
# feuerbird_add_library() directly.

# ===========================================================================
# STATUS MESSAGE
# ===========================================================================

message(STATUS "FeuerBird Exokernel Configuration Module loaded")

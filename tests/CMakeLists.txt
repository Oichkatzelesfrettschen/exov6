cmake_minimum_required(VERSION 3.16)
project(ExoTests C)

enable_testing()

set(CMAKE_C_STANDARD 17)
set(CMAKE_C_STANDARD_REQUIRED ON)

# ═════════════════════════════════════════════════════════════════════
# COMMON TEST FRAMEWORK
# ═════════════════════════════════════════════════════════════════════

# Common Test Framework
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/unit/test_framework.c")
    add_library(test_framework STATIC unit/test_framework.c)
    target_include_directories(test_framework PUBLIC
        ${CMAKE_CURRENT_SOURCE_DIR}/unit
        ${CMAKE_CURRENT_SOURCE_DIR}
        ${CMAKE_CURRENT_SOURCE_DIR}/../include
    )
endif()

# ═════════════════════════════════════════════════════════════════════
# C17 TEST SUITE
# ═════════════════════════════════════════════════════════════════════

# Add C17 test subdirectory
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/c17")
    add_subdirectory(c17)
    set(C17_TESTS_AVAILABLE TRUE)
endif()

# Add Architecture Memory tests
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/arch_mem" AND CMAKE_SYSTEM_PROCESSOR MATCHES "x86_64|amd64")
    add_subdirectory(arch_mem)
endif()

# ═════════════════════════════════════════════════════════════════════
# TEST HOST STUBS
# ═════════════════════════════════════════════════════════════════════

if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/libos_host_stubs.c")
    add_library(phoenix-test-host-stubs STATIC libos_host_stubs.c)
    target_include_directories(phoenix-test-host-stubs PUBLIC
        ${CMAKE_CURRENT_SOURCE_DIR}
        ${CMAKE_SOURCE_DIR}/include
    )
endif()

# Unit Tests
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/unit")
    add_subdirectory(unit)
endif()

# Kernel Tests
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/kernel")
    add_subdirectory(kernel)
endif()

# POSIX Tests
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/posix")
    add_subdirectory(posix)
endif()

# Performance Tests
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/perf")
    add_subdirectory(perf)
endif()

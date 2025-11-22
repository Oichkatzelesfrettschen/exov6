cmake_minimum_required(VERSION 3.16)
project(ExoTests C)

enable_testing()

set(CMAKE_C_STANDARD 17)
set(CMAKE_C_STANDARD_REQUIRED ON)

# Common Test Framework
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/unit/test_framework.c")
    add_library(test_framework STATIC unit/test_framework.c)
    target_include_directories(test_framework PUBLIC
        ${CMAKE_CURRENT_SOURCE_DIR}/unit
        ${CMAKE_CURRENT_SOURCE_DIR}
        ${CMAKE_CURRENT_SOURCE_DIR}/../include
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

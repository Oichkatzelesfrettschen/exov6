# Minimal test CMakeLists.txt
cmake_minimum_required(VERSION 3.16)

if(NOT DEFINED CMAKE_C_COMPILER)
    set(CMAKE_C_COMPILER clang)
endif()

project(ExoV6Test LANGUAGES C)

set(CMAKE_MODULE_PATH "${CMAKE_SOURCE_DIR}/cmake")
include(ExoV6Config)

# Test simple library creation
exov6_add_library(test-lib
    STATIC
    SOURCES src/arch/simd_dispatch.c
    INCLUDES ${CMAKE_SOURCE_DIR}/include
)

message(STATUS "Test library created successfully")
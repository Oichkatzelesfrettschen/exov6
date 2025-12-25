# POSIX 2024 Compliance Test Suite
cmake_minimum_required(VERSION 3.16)

# C17 standard enforcement for POSIX 2024 compliance
set(CMAKE_C_STANDARD 17)
set(CMAKE_C_STANDARD_REQUIRED ON)
set(CMAKE_C_EXTENSIONS OFF)

# Compiler flags for POSIX compatibility tests
set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} -Wall -Werror -Wextra")
set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} -D_POSIX_C_SOURCE=200809L")
set(CMAKE_C_FLAGS_DEBUG "-g -O0")
set(CMAKE_C_FLAGS_RELEASE "-O2")

# Include directories
include_directories(
    ${CMAKE_SOURCE_DIR}/../../include
    ${CMAKE_SOURCE_DIR}/../../kernel
    ${CMAKE_SOURCE_DIR}/../../libos
    ${CMAKE_SOURCE_DIR}/../../libos/posix2024
)

# POSIX compatibility test executable
add_executable(test_posix_compatibility
    test_posix_compatibility.c
)

# Link against required libraries
target_link_libraries(test_posix_compatibility
    # Will link against LibOS POSIX implementation when available
    m  # Math library for performance calculations
    pthread  # For thread tests
)

# Register test with CTest
add_test(
    NAME posix2024_compatibility
    COMMAND test_posix_compatibility
    WORKING_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}
)

# Set test properties
set_tests_properties(posix2024_compatibility PROPERTIES
    TIMEOUT 300  # 5 minute timeout
    LABELS "posix;compatibility;integration"
)

# Custom target for running only POSIX tests
add_custom_target(run-posix-tests
    COMMAND ${CMAKE_CTEST_COMMAND} -L posix --output-on-failure
    DEPENDS test_posix_compatibility
    WORKING_DIRECTORY ${CMAKE_BINARY_DIR}
    COMMENT "Running POSIX 2024 compatibility tests"
)

# Performance benchmark target
add_custom_target(posix-benchmark
    COMMAND test_posix_compatibility --benchmark
    DEPENDS test_posix_compatibility
    WORKING_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}
    COMMENT "Running POSIX compatibility performance benchmarks"
)

# Install test binary (optional)
install(TARGETS test_posix_compatibility
    RUNTIME DESTINATION bin/tests
    COMPONENT tests
)
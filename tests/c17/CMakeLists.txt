# C17 Test Suite - Pure CMake Build System
cmake_minimum_required(VERSION 3.16)
project(FeuerBirdExokernelTests LANGUAGES C)

# C17 standard enforcement
set(CMAKE_C_STANDARD 17)
set(CMAKE_C_STANDARD_REQUIRED ON)
set(CMAKE_C_EXTENSIONS OFF)

# Compiler flags for tests
set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} -Wall -Werror -Wextra")
set(CMAKE_C_FLAGS_DEBUG "-g -O0 -fsanitize=address,undefined")
set(CMAKE_C_FLAGS_RELEASE "-O2")

# Include directories - use CMAKE_SOURCE_DIR (project root)
# Note: When included via add_subdirectory, CMAKE_SOURCE_DIR is project root
include_directories(
    ${CMAKE_SOURCE_DIR}/include
    ${CMAKE_SOURCE_DIR}/kernel
    ${CMAKE_SOURCE_DIR}/libos
    ${CMAKE_BINARY_DIR}/include
)

# Test framework library
add_library(test_framework STATIC
    test_framework.c
)

# Add subdirectories for test categories
add_subdirectory(unit)
add_subdirectory(integration)
add_subdirectory(posix)
add_subdirectory(performance)

# Enable CTest
enable_testing()

# Custom target to run all tests
add_custom_target(run-c17-tests
    COMMAND ${CMAKE_CTEST_COMMAND} --output-on-failure
    DEPENDS all_tests
    WORKING_DIRECTORY ${CMAKE_BINARY_DIR}
    COMMENT "Running all C17 tests"
)

# Generate C17 test report
add_custom_target(c17-test-report
    COMMAND ${CMAKE_CTEST_COMMAND} --output-on-failure --verbose
    COMMAND ${CMAKE_COMMAND} -E echo "C17 test execution complete"
    DEPENDS all_tests
    WORKING_DIRECTORY ${CMAKE_BINARY_DIR}
    COMMENT "Generating C17 test report"
)
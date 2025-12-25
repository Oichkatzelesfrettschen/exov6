# FeuerBird Exokernel Test Suite
cmake_minimum_required(VERSION 3.16)

# Test categories
add_subdirectory(c17)
add_subdirectory(ipc)
add_subdirectory(kernel)

# POSIX 2024 compatibility tests
add_subdirectory(posix2024-compliance)

# Multi-personality tests
add_subdirectory(personality)

# Enable testing
enable_testing()

# Master test target
add_custom_target(run-all-tests
    COMMAND ${CMAKE_CTEST_COMMAND} --output-on-failure --verbose
    WORKING_DIRECTORY ${CMAKE_BINARY_DIR}
    COMMENT "Running complete FeuerBird test suite"
)
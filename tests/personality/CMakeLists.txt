# Multi-Personality Test Suite
cmake_minimum_required(VERSION 3.16)

# Integration test for multi-personality gateway
add_executable(test_multi_personality
    test_multi_personality.c
    ${CMAKE_SOURCE_DIR}/kernel/sys/syscall_gateway.c
    ${CMAKE_SOURCE_DIR}/kernel/sys/abi_versioning.c
)

target_include_directories(test_multi_personality PRIVATE
    ${CMAKE_SOURCE_DIR}/kernel
    ${CMAKE_SOURCE_DIR}/kernel/sys
    ${CMAKE_SOURCE_DIR}/include
)

target_compile_definitions(test_multi_personality PRIVATE
    TESTING_MODE=1
)

# Personality detection test
add_executable(test_personality_detection
    test_personality_detection.c
    ${CMAKE_SOURCE_DIR}/kernel/sys/elf_personality.c
    ${CMAKE_SOURCE_DIR}/kernel/sys/syscall_gateway.c
)

target_include_directories(test_personality_detection PRIVATE
    ${CMAKE_SOURCE_DIR}/kernel
    ${CMAKE_SOURCE_DIR}/kernel/sys
    ${CMAKE_SOURCE_DIR}/include
)

# Build personality-specific test binaries
add_custom_target(build_personality_binaries
    COMMAND ${CMAKE_CURRENT_SOURCE_DIR}/build_test_binaries.sh
    WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
    COMMENT "Building personality-specific test binaries"
)

# Linux personality test binary
add_executable(test_linux_binary test_linux_binary.c)
set_target_properties(test_linux_binary PROPERTIES
    OUTPUT_NAME test_linux
    RUNTIME_OUTPUT_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}/binaries
)

# BSD personality test binary
add_executable(test_bsd_binary test_bsd_binary.c)
set_target_properties(test_bsd_binary PROPERTIES
    OUTPUT_NAME test_bsd
    RUNTIME_OUTPUT_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}/binaries
)

# Illumos personality test binary
add_executable(test_illumos_binary test_illumos_binary.c)
set_target_properties(test_illumos_binary PROPERTIES
    OUTPUT_NAME test_illumos
    RUNTIME_OUTPUT_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}/binaries
)

# V6/V7 compatibility test binary
add_executable(test_v6_binary test_v6_binary.c)
set_target_properties(test_v6_binary PROPERTIES
    OUTPUT_NAME test_v6
    RUNTIME_OUTPUT_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}/binaries
)

# Add tests to CTest
add_test(NAME multi_personality_gateway
    COMMAND test_multi_personality
)

add_test(NAME personality_detection
    COMMAND test_personality_detection
)

add_test(NAME personality_binaries
    COMMAND ${CMAKE_CURRENT_SOURCE_DIR}/run_personality_tests.sh
    WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
)

# Set test properties
set_tests_properties(multi_personality_gateway PROPERTIES
    LABELS "personality;syscall"
    TIMEOUT 30
)

set_tests_properties(personality_detection PROPERTIES
    LABELS "personality;elf"
    TIMEOUT 30
    DEPENDS build_personality_binaries
)

set_tests_properties(personality_binaries PROPERTIES
    LABELS "personality;integration"
    TIMEOUT 60
    DEPENDS build_personality_binaries
)

# Performance benchmark for personality switching
add_executable(benchmark_personality_switch
    benchmark_personality_switch.c
    ${CMAKE_SOURCE_DIR}/kernel/sys/syscall_gateway.c
    ${CMAKE_SOURCE_DIR}/kernel/sys/abi_versioning.c
)

target_include_directories(benchmark_personality_switch PRIVATE
    ${CMAKE_SOURCE_DIR}/kernel
    ${CMAKE_SOURCE_DIR}/kernel/sys
    ${CMAKE_SOURCE_DIR}/include
)

# Custom target to run all personality tests
add_custom_target(test-personalities
    COMMAND ${CMAKE_CTEST_COMMAND} -L personality --output-on-failure
    WORKING_DIRECTORY ${CMAKE_BINARY_DIR}
    DEPENDS test_multi_personality test_personality_detection build_personality_binaries
    COMMENT "Running all multi-personality tests"
)
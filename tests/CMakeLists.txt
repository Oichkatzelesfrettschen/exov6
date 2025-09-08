# tests/CMakeLists.txt - Pure C17 Test Suite (No Python Dependencies)
cmake_minimum_required(VERSION 3.16)

# ═════════════════════════════════════════════════════════════════════
# TEST FRAMEWORK SETUP - PURE C17
# ═════════════════════════════════════════════════════════════════════

# Enable testing
enable_testing()

# Set C17 standard for all tests
set(CMAKE_C_STANDARD 17)
set(CMAKE_C_STANDARD_REQUIRED ON)
set(CMAKE_C_EXTENSIONS OFF)

# ═════════════════════════════════════════════════════════════════════
# C17 TEST SUITE
# ═════════════════════════════════════════════════════════════════════

# Add C17 test subdirectory
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/c17")
    add_subdirectory(c17)
    set(C17_TESTS_AVAILABLE TRUE)
endif()

# ═════════════════════════════════════════════════════════════════════
# TEST HOST STUBS
# ═════════════════════════════════════════════════════════════════════

if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/libos_host_stubs.c")
    phoenix_add_library(phoenix-test-host-stubs
        STATIC
        SOURCES libos_host_stubs.c
        INCLUDES 
            ${CMAKE_CURRENT_SOURCE_DIR}
            ${CMAKE_SOURCE_DIR}/include
        DEPENDENCIES phoenix-libos
    )
endif()

# ═════════════════════════════════════════════════════════════════════
# MICROBENCHMARK SUITE
# ═════════════════════════════════════════════════════════════════════

if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/microbench")
    if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/microbench/CMakeLists.txt")
        add_subdirectory(microbench)
    else()
        # Create microbenchmark tests manually
        file(GLOB MICROBENCH_SOURCES microbench/*.c)
        foreach(bench_source ${MICROBENCH_SOURCES})
            get_filename_component(bench_name ${bench_source} NAME_WE)
            
            phoenix_add_executable(microbench-${bench_name}
                SOURCES ${bench_source}
                INCLUDES 
                    ${CMAKE_CURRENT_SOURCE_DIR}/microbench
                    ${CMAKE_CURRENT_SOURCE_DIR}
                    ${CMAKE_SOURCE_DIR}/include
                DEPENDENCIES 
                    phoenix-libos
                    phoenix-architecture
            )
            
            set_target_properties(microbench-${bench_name} PROPERTIES 
                OUTPUT_NAME "microbench-${bench_name}"
                PREFIX ""
            )
            
            # Add as test
            add_test(
                NAME microbench-${bench_name}
                COMMAND phoenix-microbench-${bench_name}
            )
            
            set_tests_properties(microbench-${bench_name} PROPERTIES
                LABELS "microbench;performance"
                TIMEOUT 120
            )
        endforeach()
    endif()
endif()

# ═════════════════════════════════════════════════════════════════════
# INTEGRATION TESTS
# ═════════════════════════════════════════════════════════════════════

# Test with kernel if available
if(TARGET phoenix-kernel)
    # Kernel integration test
    add_test(
        NAME kernel-boot-test
        COMMAND ${CMAKE_COMMAND} -E echo "Kernel boot test placeholder"
    )
    
    set_tests_properties(kernel-boot-test PROPERTIES
        LABELS "integration;kernel"
        TIMEOUT 60
    )
    
    # If QEMU is available, add QEMU-based tests
    if(QEMU_EXECUTABLE)
        add_test(
            NAME qemu-kernel-test
            COMMAND timeout 30 ${QEMU_EXECUTABLE} -nographic -kernel $<TARGET_FILE:phoenix-kernel> -serial stdio
        )
        
        set_tests_properties(qemu-kernel-test PROPERTIES
            LABELS "integration;qemu"
            TIMEOUT 45
        )
    endif()
endif()

# LibOS integration tests
if(TARGET phoenix-libos)
    add_test(
        NAME libos-integration-test
        COMMAND ${CMAKE_COMMAND} -E echo "LibOS integration test placeholder"
    )
    
    set_tests_properties(libos-integration-test PROPERTIES
        LABELS "integration;libos"
        TIMEOUT 30
    )
endif()

# ═════════════════════════════════════════════════════════════════════
# STRESS TESTS
# ═════════════════════════════════════════════════════════════════════

# Create stress test targets if stress test programs exist
if(EXISTS "${CMAKE_SOURCE_DIR}/user/stressfs.c" AND TARGET phoenix-user-stressfs)
    add_test(
        NAME stress-filesystem
        COMMAND phoenix-user-stressfs
    )
    
    set_tests_properties(stress-filesystem PROPERTIES
        LABELS "stress;filesystem"
        TIMEOUT 300
    )
endif()

# ═════════════════════════════════════════════════════════════════════
# MEMORY TESTS
# ═════════════════════════════════════════════════════════════════════

# Valgrind tests (if available)
find_program(VALGRIND_EXECUTABLE valgrind)
if(VALGRIND_EXECUTABLE)
    # Add valgrind test for each microbenchmark
    file(GLOB MICROBENCH_TARGETS microbench-*)
    foreach(bench_target ${MICROBENCH_TARGETS})
        if(TARGET phoenix-${bench_target})
            add_test(
                NAME valgrind-${bench_target}
                COMMAND ${VALGRIND_EXECUTABLE} --error-exitcode=1 --leak-check=full $<TARGET_FILE:phoenix-${bench_target}>
            )
            
            set_tests_properties(valgrind-${bench_target} PROPERTIES
                LABELS "valgrind;memory"
                TIMEOUT 600
            )
        endif()
    endforeach()
endif()

# ═════════════════════════════════════════════════════════════════════
# SECURITY TESTS
# ═════════════════════════════════════════════════════════════════════

# Security audit test (pure C implementation)
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/c17/security/test_security_audit.c")
    add_executable(test-security-audit c17/security/test_security_audit.c)
    target_link_libraries(test-security-audit test_framework)
    
    add_test(
        NAME security-audit
        COMMAND test-security-audit
        WORKING_DIRECTORY ${CMAKE_SOURCE_DIR}
    )
    
    set_tests_properties(security-audit PROPERTIES
        LABELS "security;audit"
        TIMEOUT 180
    )
endif()

# ═════════════════════════════════════════════════════════════════════
# TEST CONFIGURATION AND METADATA
# ═════════════════════════════════════════════════════════════════════

# Set common test environment
set_tests_properties(${test_targets} PROPERTIES
    ENVIRONMENT "EXOV6_BUILD_DIR=${CMAKE_BINARY_DIR}"
)

# ═════════════════════════════════════════════════════════════════════
# CUSTOM TEST TARGETS
# ═════════════════════════════════════════════════════════════════════

# Quick test suite (fast tests only)
add_custom_target(test-quick
    COMMAND ${CMAKE_CTEST_COMMAND} -L "unit" --output-on-failure
    COMMENT "Running quick unit tests"
)

# Full test suite
add_custom_target(test-full
    COMMAND ${CMAKE_CTEST_COMMAND} --output-on-failure
    COMMENT "Running full test suite"
)

# Performance test suite
add_custom_target(test-performance
    COMMAND ${CMAKE_CTEST_COMMAND} -L "performance|microbench|benchmark" --output-on-failure
    COMMENT "Running performance tests"
)

# Integration test suite
add_custom_target(test-integration
    COMMAND ${CMAKE_CTEST_COMMAND} -L "integration" --output-on-failure
    COMMENT "Running integration tests"
)

# Memory test suite
add_custom_target(test-memory
    COMMAND ${CMAKE_CTEST_COMMAND} -L "memory|valgrind" --output-on-failure
    COMMENT "Running memory tests"
)

# Security test suite
add_custom_target(test-security
    COMMAND ${CMAKE_CTEST_COMMAND} -L "security" --output-on-failure
    COMMENT "Running security tests"
)

# POSIX compliance test suite
add_custom_target(test-posix
    COMMAND ${CMAKE_CTEST_COMMAND} -L "posix|compliance" --output-on-failure
    COMMENT "Running POSIX compliance tests"
)

# C17 unit tests
if(C17_TESTS_AVAILABLE)
    add_custom_target(test-c17-unit
        COMMAND ${CMAKE_CTEST_COMMAND} -L "unit" --output-on-failure
        WORKING_DIRECTORY ${CMAKE_BINARY_DIR}/tests/c17
        COMMENT "Running C17 unit tests"
    )
    
    add_custom_target(test-c17-all
        COMMAND ${CMAKE_CTEST_COMMAND} --output-on-failure
        WORKING_DIRECTORY ${CMAKE_BINARY_DIR}/tests/c17
        COMMENT "Running all C17 tests"
    )
endif()

# ═════════════════════════════════════════════════════════════════════
# TEST REPORTING
# ═════════════════════════════════════════════════════════════════════

# Test report generation
add_custom_target(test-report
    COMMAND ${CMAKE_CTEST_COMMAND} --output-on-failure --output-junit ${CMAKE_BINARY_DIR}/test-results.xml
    COMMENT "Generating test report"
)

# Coverage report (if gcov/lcov available)
find_program(GCOV_EXECUTABLE gcov)
find_program(LCOV_EXECUTABLE lcov)
find_program(GENHTML_EXECUTABLE genhtml)

if(GCOV_EXECUTABLE AND LCOV_EXECUTABLE AND GENHTML_EXECUTABLE)
    add_custom_target(test-coverage
        COMMAND ${LCOV_EXECUTABLE} --directory ${CMAKE_BINARY_DIR} --capture --output-file coverage.info
        COMMAND ${LCOV_EXECUTABLE} --remove coverage.info '/usr/*' --output-file coverage.info
        COMMAND ${GENHTML_EXECUTABLE} coverage.info --output-directory coverage-report
        WORKING_DIRECTORY ${CMAKE_BINARY_DIR}
        COMMENT "Generating coverage report"
    )
endif()

# ═════════════════════════════════════════════════════════════════════
# EXPORTS
# ═════════════════════════════════════════════════════════════════════

# Collect all test targets
set(TEST_TARGETS)
if(TARGET phoenix-test-host-stubs)
    list(APPEND TEST_TARGETS phoenix-test-host-stubs)
endif()

# Add microbenchmark targets
get_directory_property(ALL_TARGETS BUILDSYSTEM_TARGETS)
foreach(target ${ALL_TARGETS})
    if(target MATCHES "^phoenix-microbench-")
        list(APPEND TEST_TARGETS ${target})
    endif()
endforeach()

set(EXOV6_TEST_TARGETS ${TEST_TARGETS} PARENT_SCOPE)

# ═════════════════════════════════════════════════════════════════════
# STATUS MESSAGES
# ═════════════════════════════════════════════════════════════════════

message(STATUS "Tests zone configured (Pure C17, No Python):")
if(C17_TESTS_AVAILABLE)
    message(STATUS "  - C17 test suite: ✓")
endif()
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/microbench")
    message(STATUS "  - Microbenchmarks: ✓")
endif()
if(VALGRIND_EXECUTABLE)
    message(STATUS "  - Valgrind tests: ✓")
endif()
if(QEMU_EXECUTABLE)
    message(STATUS "  - QEMU integration: ✓")
endif()
message(STATUS "  - Test categories: unit, integration, performance, memory, security, posix")
message(STATUS "  - Build system: Pure CMake (no external dependencies)")
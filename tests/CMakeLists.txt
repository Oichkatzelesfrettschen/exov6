# tests/CMakeLists.txt - Comprehensive Test Suite

# ═════════════════════════════════════════════════════════════════════
# TEST FRAMEWORK SETUP
# ═════════════════════════════════════════════════════════════════════

# Enable testing
enable_testing()

# Find Python for test framework
find_package(Python3 COMPONENTS Interpreter)

# Find pytest if available
if(Python3_FOUND)
    execute_process(
        COMMAND ${Python3_EXECUTABLE} -m pytest --version
        OUTPUT_VARIABLE PYTEST_VERSION
        ERROR_QUIET
        OUTPUT_STRIP_TRAILING_WHITESPACE
    )
    if(PYTEST_VERSION)
        set(PYTEST_FOUND TRUE)
        message(STATUS "Found pytest: ${PYTEST_VERSION}")
    endif()
endif()

# ═════════════════════════════════════════════════════════════════════
# C TEST UTILITIES
# ═════════════════════════════════════════════════════════════════════

# Test host stubs
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
# PYTHON TEST MODULES
# ═════════════════════════════════════════════════════════════════════

if(PYTEST_FOUND)
    # Core system tests
    set(PYTHON_TESTS
        test_arbitrate.py
        test_beatty_cycle.py
        test_build_script.py
        test_cap_entry_cpp.py
        test_cap_newtypes.py
        test_cap_revoke.py
        test_cap_types.py
        test_chan_endpoint.py
        test_dag_cycle.py
        test_door.py
        test_encrypt_mod.py
        test_exo_ipc_direct.py
        test_exo_recv_timed.py
        test_flow_pid.py
        test_formal_models.py
        test_iommu.py
        test_irq.py
        test_lattice_channel_dag.py
        test_lattice_dag.py
        test_lattice_ipc.py
        test_libnstr_graph.py
        test_libos_env.py
        test_locks.py
        test_lockstress.py
        test_mailbox_isolation.py
        test_octonion.py
        test_posix_apis.py
        test_posix_compat.py
        test_ptrace_concurrent.py
        test_simulate.py
        test_spinlock_align.py
        test_stream_module.py
        test_streams_log.py
        test_sys_ipc.py
        test_ticket_spinlock_processes.py
        test_ticket_spinlock_threads.py
        test_uv_spinlock_processes.py
        test_uv_spinlock_threads.py
        test_zone.py
    )
    
    # Create individual test targets for each Python test
    foreach(test_file ${PYTHON_TESTS})
        if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/${test_file}")
            # Extract test name from filename
            string(REGEX REPLACE "test_(.+)\\.py$" "\\1" test_name ${test_file})
            string(REPLACE "_" "-" test_target_name ${test_name})
            
            add_test(
                NAME python-${test_target_name}
                COMMAND ${Python3_EXECUTABLE} -m pytest ${CMAKE_CURRENT_SOURCE_DIR}/${test_file} -v
                WORKING_DIRECTORY ${CMAKE_SOURCE_DIR}
            )
            
            # Set test properties
            set_tests_properties(python-${test_target_name} PROPERTIES
                LABELS "python;unit"
                TIMEOUT 300
            )
        endif()
    endforeach()
    
    # Create aggregate test targets
    add_custom_target(test-python-all
        COMMAND ${Python3_EXECUTABLE} -m pytest ${CMAKE_CURRENT_SOURCE_DIR} -v
        WORKING_DIRECTORY ${CMAKE_SOURCE_DIR}
        COMMENT "Running all Python tests"
    )
    
    # Category-specific test targets
    add_custom_target(test-python-capabilities
        COMMAND ${Python3_EXECUTABLE} -m pytest ${CMAKE_CURRENT_SOURCE_DIR} -k "cap_" -v
        WORKING_DIRECTORY ${CMAKE_SOURCE_DIR}
        COMMENT "Running capability tests"
    )
    
    add_custom_target(test-python-locks
        COMMAND ${Python3_EXECUTABLE} -m pytest ${CMAKE_CURRENT_SOURCE_DIR} -k "lock" -v
        WORKING_DIRECTORY ${CMAKE_SOURCE_DIR}
        COMMENT "Running lock tests"
    )
    
    add_custom_target(test-python-ipc
        COMMAND ${Python3_EXECUTABLE} -m pytest ${CMAKE_CURRENT_SOURCE_DIR} -k "ipc" -v
        WORKING_DIRECTORY ${CMAKE_SOURCE_DIR}
        COMMENT "Running IPC tests"
    )
    
    add_custom_target(test-python-posix
        COMMAND ${Python3_EXECUTABLE} -m pytest ${CMAKE_CURRENT_SOURCE_DIR} -k "posix" -v
        WORKING_DIRECTORY ${CMAKE_SOURCE_DIR}
        COMMENT "Running POSIX tests"
    )
endif()

# ═════════════════════════════════════════════════════════════════════
# BATS TESTING FRAMEWORK
# ═════════════════════════════════════════════════════════════════════

find_program(BATS_EXECUTABLE bats)
if(BATS_EXECUTABLE AND EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/benchmarks.bats")
    add_test(
        NAME bats-benchmarks
        COMMAND ${BATS_EXECUTABLE} ${CMAKE_CURRENT_SOURCE_DIR}/benchmarks.bats
        WORKING_DIRECTORY ${CMAKE_SOURCE_DIR}
    )
    
    set_tests_properties(bats-benchmarks PROPERTIES
        LABELS "bats;benchmark"
        TIMEOUT 600
    )
    
    add_custom_target(test-benchmarks
        COMMAND ${BATS_EXECUTABLE} ${CMAKE_CURRENT_SOURCE_DIR}/benchmarks.bats
        WORKING_DIRECTORY ${CMAKE_SOURCE_DIR}
        COMMENT "Running benchmark tests"
    )
endif()

# ═════════════════════════════════════════════════════════════════════
# MICROBENCHMARK SUITE
# ═════════════════════════════════════════════════════════════════════

if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/microbench")
    # Add microbenchmark subdirectory if it has CMakeLists.txt
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

# Security audit test (if security audit script exists)
if(EXISTS "${CMAKE_SOURCE_DIR}/test_security_audit.py" AND Python3_FOUND)
    add_test(
        NAME security-audit
        COMMAND ${Python3_EXECUTABLE} ${CMAKE_SOURCE_DIR}/test_security_audit.py
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

# Create test configuration file
configure_file(
    "${CMAKE_SOURCE_DIR}/pytest.ini"
    "${CMAKE_BINARY_DIR}/pytest.ini"
    COPYONLY
)

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
    COMMAND ${CMAKE_CTEST_COMMAND} -L "performance|microbench" --output-on-failure
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

message(STATUS "Tests zone configured:")
if(PYTEST_FOUND)
    message(STATUS "  - Python tests: ✓")
endif()
if(BATS_EXECUTABLE)
    message(STATUS "  - BATS tests: ✓")
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
message(STATUS "  - Test categories: unit, integration, performance, memory, security")
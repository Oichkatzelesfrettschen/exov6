# Multi-Personality Test Suite
cmake_minimum_required(VERSION 3.16)

# ═════════════════════════════════════════════════════════════════════
# HELPER MACRO: Conditionally add executable if source exists
# ═════════════════════════════════════════════════════════════════════
macro(add_personality_test name)
    if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/${name}.c")
        add_executable(${name} ${ARGN})
        set(${name}_EXISTS TRUE)
    else()
        message(STATUS "Personality test ${name} skipped - source not found")
        set(${name}_EXISTS FALSE)
    endif()
endmacro()

# ═════════════════════════════════════════════════════════════════════
# INTEGRATION TESTS
# ═════════════════════════════════════════════════════════════════════
# NOTE: Kernel integration tests (test_multi_personality, test_personality_detection)
# require full kernel infrastructure including x86 intrinsics and kernel struct
# definitions. These cannot be built as host tests - they need QEMU/emulator.
# They are disabled until proper kernel test framework is available.

message(STATUS "Kernel integration tests disabled - require QEMU test harness")
set(test_multi_personality_EXISTS FALSE)
set(test_personality_detection_EXISTS FALSE)

# ═════════════════════════════════════════════════════════════════════
# PERSONALITY-SPECIFIC TEST BINARIES
# ═════════════════════════════════════════════════════════════════════

# Build personality-specific test binaries script
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/build_test_binaries.sh")
    add_custom_target(build_personality_binaries
        COMMAND ${CMAKE_CURRENT_SOURCE_DIR}/build_test_binaries.sh
        WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
        COMMENT "Building personality-specific test binaries"
    )
endif()

# Linux personality test binary
add_personality_test(test_linux_binary test_linux_binary.c)
if(test_linux_binary_EXISTS)
    set_target_properties(test_linux_binary PROPERTIES
        OUTPUT_NAME test_linux
        RUNTIME_OUTPUT_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}/binaries
    )
endif()

# BSD personality test binary - only build on BSD systems
if(CMAKE_SYSTEM_NAME MATCHES "BSD|DragonFly")
    add_personality_test(test_bsd_binary test_bsd_binary.c)
    if(test_bsd_binary_EXISTS)
        set_target_properties(test_bsd_binary PROPERTIES
            OUTPUT_NAME test_bsd
            RUNTIME_OUTPUT_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}/binaries
        )
    endif()
else()
    message(STATUS "Skipping BSD personality test - not on BSD system")
endif()

# Illumos personality test binary - only build on Illumos/Solaris
if(CMAKE_SYSTEM_NAME MATCHES "SunOS|Solaris")
    add_personality_test(test_illumos_binary test_illumos_binary.c)
    if(test_illumos_binary_EXISTS)
        set_target_properties(test_illumos_binary PROPERTIES
            OUTPUT_NAME test_illumos
            RUNTIME_OUTPUT_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}/binaries
        )
    endif()
else()
    message(STATUS "Skipping Illumos personality test - not on Illumos/Solaris")
endif()

# FeuerBird V6/V7 compatibility test binary
add_personality_test(test_v6_binary test_v6_binary.c)
if(test_v6_binary_EXISTS)
    set_target_properties(test_v6_binary PROPERTIES
        OUTPUT_NAME test_feuerbird_v6
        RUNTIME_OUTPUT_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}/binaries
    )
endif()

# ═════════════════════════════════════════════════════════════════════
# CTEST INTEGRATION
# ═════════════════════════════════════════════════════════════════════

if(test_multi_personality_EXISTS)
    add_test(NAME multi_personality_gateway
        COMMAND test_multi_personality
    )
    set_tests_properties(multi_personality_gateway PROPERTIES
        LABELS "personality;syscall"
        TIMEOUT 30
    )
endif()

if(test_personality_detection_EXISTS)
    add_test(NAME personality_detection
        COMMAND test_personality_detection
    )
    set_tests_properties(personality_detection PROPERTIES
        LABELS "personality;elf"
        TIMEOUT 30
    )
endif()

if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/run_personality_tests.sh")
    add_test(NAME personality_binaries
        COMMAND ${CMAKE_CURRENT_SOURCE_DIR}/run_personality_tests.sh
        WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
    )
    set_tests_properties(personality_binaries PROPERTIES
        LABELS "personality;integration"
        TIMEOUT 60
    )
endif()

# ═════════════════════════════════════════════════════════════════════
# PERFORMANCE BENCHMARKS
# ═════════════════════════════════════════════════════════════════════
# NOTE: Kernel benchmarks disabled - require QEMU test harness

message(STATUS "Kernel benchmarks disabled - require QEMU test harness")
set(benchmark_personality_switch_EXISTS FALSE)

# ═════════════════════════════════════════════════════════════════════
# CUSTOM TARGETS
# ═════════════════════════════════════════════════════════════════════

# Collect available test targets
set(PERSONALITY_TEST_TARGETS)
if(test_multi_personality_EXISTS)
    list(APPEND PERSONALITY_TEST_TARGETS test_multi_personality)
endif()
if(test_personality_detection_EXISTS)
    list(APPEND PERSONALITY_TEST_TARGETS test_personality_detection)
endif()

# Custom target to run all personality tests
if(PERSONALITY_TEST_TARGETS)
    add_custom_target(test-personalities
        COMMAND ${CMAKE_CTEST_COMMAND} -L personality --output-on-failure
        WORKING_DIRECTORY ${CMAKE_BINARY_DIR}
        DEPENDS ${PERSONALITY_TEST_TARGETS}
        COMMENT "Running all multi-personality tests"
    )
else()
    message(STATUS "No personality tests available - skipping test-personalities target")
endif()

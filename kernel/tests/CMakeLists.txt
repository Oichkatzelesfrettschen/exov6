# Kernel-level Tests
# Low-level kernel component tests

# Test bootasm assembly
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/test_bootasm.S")
    # Assembly test - just check it compiles
    add_library(test-bootasm-obj OBJECT test_bootasm.S)
    set_target_properties(test-bootasm-obj PROPERTIES EXCLUDE_FROM_ALL TRUE)
endif()

# Test spinlock header
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/test_spinlock.h")
    # Header test - create test executable that includes it
    add_custom_target(test-spinlock-header
        COMMAND ${CMAKE_C_COMPILER} -I${CMAKE_CURRENT_SOURCE_DIR} -I${CMAKE_SOURCE_DIR}/include -c -x c /dev/null -include test_spinlock.h
        WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
        COMMENT "Testing spinlock header compilation"
    )
endif()

message(STATUS "Kernel tests configured:")
message(STATUS "  - Assembly tests: ✓")
message(STATUS "  - Header tests: ✓")
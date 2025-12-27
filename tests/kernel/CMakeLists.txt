# Kernel Mathematical Test Suite
# Tests advanced mathematical kernel capabilities and 2025 cutting-edge concepts

# Advanced mathematics test
# NOTE: Disabled until quantum_ipc.h, lattice_capability.h, realtime_analysis.h,
# and mathematical_verification.h are implemented
# if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/test_advanced_mathematics.c")
#     feuerbird_add_executable(test-advanced-mathematics
#         SOURCES test_advanced_mathematics.c
#         INCLUDES
#             ${CMAKE_CURRENT_SOURCE_DIR}
#             ${CMAKE_SOURCE_DIR}/include
#             ${CMAKE_SOURCE_DIR}/kernel
#             ${CMAKE_SOURCE_DIR}/formal
#         DEPENDENCIES feuerbird-libos
#     )
#
#     target_link_libraries(test-advanced-mathematics PRIVATE m)
#     target_compile_features(test-advanced-mathematics PRIVATE c_std_17)
#
#     set_target_properties(test-advanced-mathematics PROPERTIES
#         OUTPUT_NAME "test-advanced-mathematics"
#         PREFIX ""
#     )
#
#     # Add as CTest
#     add_test(NAME AdvancedMathematics
#              COMMAND test-advanced-mathematics)
# endif()

# Simple mathematical test
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/test_simple_mathematical.c")
    feuerbird_add_executable(test-simple-mathematical
        SOURCES test_simple_mathematical.c
        INCLUDES
            ${CMAKE_CURRENT_SOURCE_DIR}
            ${CMAKE_SOURCE_DIR}/include
        DEPENDENCIES feuerbird-libos
    )
    
    target_link_libraries(test-simple-mathematical PRIVATE m)
    target_compile_features(test-simple-mathematical PRIVATE c_std_17)
    
    set_target_properties(test-simple-mathematical PROPERTIES 
        OUTPUT_NAME "test-simple-mathematical"
        PREFIX ""
    )
    
    # Add as CTest
    add_test(NAME SimpleMathematical 
             COMMAND test-simple-mathematical)
endif()

# Custom targets for running kernel tests
add_custom_target(run-kernel-math-tests
    COMMENT "Running kernel mathematical tests"
)

if(TARGET test-advanced-mathematics)
    add_custom_target(run-advanced-math-test
        COMMAND test-advanced-mathematics
        DEPENDS test-advanced-mathematics
        COMMENT "Running advanced mathematics test"
    )
    add_dependencies(run-kernel-math-tests run-advanced-math-test)
endif()

if(TARGET test-simple-mathematical)
    add_custom_target(run-simple-math-test
        COMMAND test-simple-mathematical
        DEPENDS test-simple-mathematical
        COMMENT "Running simple mathematical test"
    )
    add_dependencies(run-kernel-math-tests run-simple-math-test)
endif()

message(STATUS "Kernel mathematical tests configured:")
message(STATUS "  - Advanced mathematics test: DISABLED (pending quantum_ipc headers)")
message(STATUS "  - Simple mathematical test: ✓")
message(STATUS "  - 2025 cutting-edge algorithm tests: partial")
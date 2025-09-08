# Performance Tests CMakeLists.txt
cmake_minimum_required(VERSION 3.16)

# Collect all performance test source files
file(GLOB PERF_TEST_SOURCES "test_*.c")

# Create test executables
foreach(test_source ${PERF_TEST_SOURCES})
    get_filename_component(test_name ${test_source} NAME_WE)
    
    add_executable(${test_name} ${test_source})
    
    target_link_libraries(${test_name} 
        test_framework
        pthread  # Threading for benchmarks
        m        # Math library
    )
    
    # Optimize for performance tests
    target_compile_options(${test_name} PRIVATE -O3 -march=native)
    
    # Add to CTest
    add_test(NAME perf_${test_name} 
             COMMAND ${test_name}
             WORKING_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR})
    
    # Set test properties
    set_tests_properties(perf_${test_name} PROPERTIES
        TIMEOUT 120
        LABELS "performance;benchmark"
    )
endforeach()

# Aggregate target for all performance tests
add_custom_target(performance_tests 
    DEPENDS ${PERF_TEST_SOURCES}
    COMMENT "Building all performance tests"
)
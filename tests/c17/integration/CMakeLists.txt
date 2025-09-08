# Integration Tests CMakeLists.txt
cmake_minimum_required(VERSION 3.16)

# Collect all integration test source files
file(GLOB INTEGRATION_TEST_SOURCES "test_*.c")

# Create test executables
foreach(test_source ${INTEGRATION_TEST_SOURCES})
    get_filename_component(test_name ${test_source} NAME_WE)
    
    add_executable(${test_name} ${test_source})
    
    target_link_libraries(${test_name} 
        test_framework
        pthread  # Threading support
        m        # Math library
    )
    
    # Add to CTest
    add_test(NAME integration_${test_name} 
             COMMAND ${test_name}
             WORKING_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR})
    
    # Set test properties
    set_tests_properties(integration_${test_name} PROPERTIES
        TIMEOUT 60
        LABELS "integration"
    )
endforeach()

# Aggregate target for all integration tests
add_custom_target(integration_tests 
    DEPENDS ${INTEGRATION_TEST_SOURCES}
    COMMENT "Building all integration tests"
)
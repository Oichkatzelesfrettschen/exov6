# Unit Tests CMakeLists.txt
cmake_minimum_required(VERSION 3.16)

# Collect all unit test source files
file(GLOB UNIT_TEST_SOURCES "test_*.c")

# Create test executables
foreach(test_source ${UNIT_TEST_SOURCES})
    get_filename_component(test_name ${test_source} NAME_WE)
    
    add_executable(${test_name} ${test_source})
    
    target_link_libraries(${test_name} 
        test_framework
        m  # Math library
    )
    
    # Add to CTest
    add_test(NAME unit_${test_name} 
             COMMAND ${test_name}
             WORKING_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR})
    
    # Set test properties
    set_tests_properties(unit_${test_name} PROPERTIES
        TIMEOUT 30
        LABELS "unit"
    )
endforeach()

# Aggregate target for all unit tests
add_custom_target(unit_tests 
    DEPENDS ${UNIT_TEST_SOURCES}
    COMMENT "Building all unit tests"
)
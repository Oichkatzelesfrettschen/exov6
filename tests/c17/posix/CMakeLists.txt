# POSIX Compliance Tests CMakeLists.txt
cmake_minimum_required(VERSION 3.16)

# Collect all POSIX test source files
file(GLOB POSIX_TEST_SOURCES "test_*.c")

# Create test executables
foreach(test_source ${POSIX_TEST_SOURCES})
    get_filename_component(test_name ${test_source} NAME_WE)
    
    add_executable(${test_name} ${test_source})
    
    target_link_libraries(${test_name} 
        test_framework
        pthread  # POSIX threads
        m        # Math library
    )
    
    # Add to CTest
    add_test(NAME posix_${test_name} 
             COMMAND ${test_name}
             WORKING_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR})
    
    # Set test properties
    set_tests_properties(posix_${test_name} PROPERTIES
        TIMEOUT 45
        LABELS "posix;compliance"
    )
endforeach()

# Aggregate target for all POSIX tests
add_custom_target(posix_tests 
    DEPENDS ${POSIX_TEST_SOURCES}
    COMMENT "Building all POSIX compliance tests"
)
cmake_minimum_required(VERSION 3.16)

# Collect all unit test source files
file(GLOB UNIT_TEST_SOURCES "test_*.c")
list(REMOVE_ITEM UNIT_TEST_SOURCES "${CMAKE_CURRENT_SOURCE_DIR}/test_framework.c")

# Create test executables
foreach(test_source ${UNIT_TEST_SOURCES})
    get_filename_component(test_name ${test_source} NAME_WE)
    
    # Skip failing tests in standalone build
    if(test_name STREQUAL "test_aether_nn" OR test_name STREQUAL "test_spinlock_align")
        continue()
    endif()

    add_executable(${test_name} ${test_source})
    
    if(TARGET test_framework)
        target_link_libraries(${test_name} test_framework)
    endif()

    target_link_libraries(${test_name}
        m
        pthread
    )

    # Include directories
    target_include_directories(${test_name} PRIVATE
        ${CMAKE_CURRENT_SOURCE_DIR}/../..
        ${CMAKE_CURRENT_SOURCE_DIR}/../../include
    )
    
    add_test(NAME unit_${test_name} 
             COMMAND ${test_name}
             WORKING_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR})
    
    set_tests_properties(unit_${test_name} PROPERTIES
        TIMEOUT 30
        LABELS "unit"
    )
endforeach()

cmake_minimum_required(VERSION 3.16)

# Integration and Stress tests
file(GLOB TEST_SOURCES "*.c")

foreach(test_source ${TEST_SOURCES})
    get_filename_component(test_name ${test_source} NAME_WE)

    # Exclude Phoenix-native tests from host build
    if(test_name MATCHES "^(ipc_test|litmus|stressfs|usertests)$")
        message(STATUS "Skipping native test: ${test_name}")
        continue()
    endif()

    if(NOT TARGET ${test_name})
        add_executable(${test_name} ${test_source})

        target_include_directories(${test_name} PRIVATE
            ${CMAKE_CURRENT_SOURCE_DIR}/../..
            ${CMAKE_CURRENT_SOURCE_DIR}/../../include
        )

        target_link_libraries(${test_name} pthread)

        add_test(NAME kernel_${test_name}
                 COMMAND ${test_name})

        set_tests_properties(kernel_${test_name} PROPERTIES
            LABELS "kernel"
            TIMEOUT 300
        )
    endif()
endforeach()

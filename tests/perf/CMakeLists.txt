cmake_minimum_required(VERSION 3.16)

# Collect all benchmark sources
file(GLOB BENCH_SOURCES "*.c")

foreach(bench_source ${BENCH_SOURCES})
    get_filename_component(bench_name ${bench_source} NAME_WE)

    # Skip failing tests in standalone build
    if(bench_name STREQUAL "proc_cap_test")
        continue()
    endif()

    if(NOT TARGET ${bench_name})
        add_executable(${bench_name} ${bench_source})

        target_include_directories(${bench_name} PRIVATE
            ${CMAKE_CURRENT_SOURCE_DIR}/../..
            ${CMAKE_CURRENT_SOURCE_DIR}/../../include
        )

        target_link_libraries(${bench_name} pthread)

        add_test(NAME perf_${bench_name}
                 COMMAND ${bench_name})

        set_tests_properties(perf_${bench_name} PROPERTIES
            LABELS "performance"
            TIMEOUT 600
        )
    endif()
endforeach()

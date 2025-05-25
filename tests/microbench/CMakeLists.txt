add_library(microbench_common OBJECT
    ../../libos/procwrap.c
    ../../libos/capwrap.c
)

target_include_directories(microbench_common PUBLIC
    ${CMAKE_SOURCE_DIR}/libos/include
    ${CMAKE_SOURCE_DIR}/src-headers
)

set(MICROBENCH_PROGS
    cap_verify_bench
    exo_yield_to_bench
    proc_cap_test
)

foreach(prog ${MICROBENCH_PROGS})
    add_executable(${prog} ${prog}.c $<TARGET_OBJECTS:microbench_common>)
    target_include_directories(${prog} PRIVATE
        ${CMAKE_SOURCE_DIR}/libos/include
        ${CMAKE_SOURCE_DIR}/src-headers
    )
endforeach()

add_custom_target(microbench-run
    COMMAND $<TARGET_FILE:cap_verify_bench>
    COMMAND $<TARGET_FILE:exo_yield_to_bench>
    COMMAND $<TARGET_FILE:proc_cap_test>
    DEPENDS cap_verify_bench exo_yield_to_bench proc_cap_test
    WORKING_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}
)

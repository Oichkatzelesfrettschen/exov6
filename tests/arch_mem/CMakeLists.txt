# Only build arch_mem tests on x86_64/amd64 where HAL implementation exists
if(CMAKE_SYSTEM_PROCESSOR MATCHES "x86_64|amd64")
    add_executable(test-arch-mem litmus.c)

    target_include_directories(test-arch-mem PRIVATE
        ${CMAKE_SOURCE_DIR}/include
    )

    target_sources(test-arch-mem PRIVATE
        ${CMAKE_SOURCE_DIR}/src/arch/x86_64/arch_ops.c
    )

    target_link_libraries(test-arch-mem pthread)

    add_test(NAME arch-mem-litmus COMMAND test-arch-mem)
else()
    message(STATUS "Skipping test-arch-mem: Only supported on x86_64/amd64 (Tier-1)")
endif()

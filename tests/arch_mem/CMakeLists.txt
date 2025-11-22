add_executable(test-arch-mem litmus.c)

target_include_directories(test-arch-mem PRIVATE
    ${CMAKE_SOURCE_DIR}/include
)

if(CMAKE_SYSTEM_PROCESSOR MATCHES "x86_64|amd64")
    target_sources(test-arch-mem PRIVATE
        ${CMAKE_SOURCE_DIR}/src/arch/x86_64/arch_ops.c
    )
endif()

target_link_libraries(test-arch-mem pthread)

add_test(NAME arch-mem-litmus COMMAND test-arch-mem)

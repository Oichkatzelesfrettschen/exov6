# Kernel Test Suite
cmake_minimum_required(VERSION 3.16)

# Add kernel test library
add_library(kernel-tests STATIC
    minimal_test.c
)

target_include_directories(kernel-tests PRIVATE
    ${CMAKE_SOURCE_DIR}/include
    ${CMAKE_SOURCE_DIR}/kernel
)

target_compile_options(kernel-tests PRIVATE
    -std=c17
    -Wall -Wextra -Werror
)

# Assembly tests (if supported)
if(CMAKE_ASM_COMPILER)
    enable_language(ASM)
    
    add_library(kernel-asm-tests STATIC
        minimal_boot.S
        test_bootasm.S
    )
    
    target_link_libraries(kernel-tests kernel-asm-tests)
endif()

# Define test target
add_custom_target(kernel-test-suite
    DEPENDS kernel-tests
    COMMENT "Building kernel test suite"
)
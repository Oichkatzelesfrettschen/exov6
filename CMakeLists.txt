cmake_minimum_required(VERSION 3.16)
project(exov6 C)

# Force clang
if(NOT CMAKE_C_COMPILER_ID MATCHES "Clang")
    message(FATAL_ERROR "GCC is not supported; please use clang")
endif()

set(CMAKE_C_STANDARD 23)
set(CMAKE_C_STANDARD_REQUIRED ON)

find_program(CLANG_TIDY_EXE NAMES clang-tidy)
if(CLANG_TIDY_EXE)
    set(CMAKE_C_CLANG_TIDY "${CLANG_TIDY_EXE}")
endif()

add_subdirectory(libnstr_graph)
# TODO: add kernel and userland targets

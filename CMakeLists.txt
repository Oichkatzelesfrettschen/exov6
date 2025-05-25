cmake_minimum_required(VERSION 3.16)
project(xv6 LANGUAGES C CXX)

set(CMAKE_C_STANDARD 23)
set(CMAKE_C_STANDARD_REQUIRED ON)
set(CMAKE_CXX_STANDARD 23)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

if(NOT CMAKE_C_COMPILER_ID MATCHES "Clang")
  message(WARNING "Clang is recommended for building this project")
endif()

find_program(CLANG_TIDY_EXE NAMES clang-tidy)
if(CLANG_TIDY_EXE)
  set(CMAKE_C_CLANG_TIDY "${CLANG_TIDY_EXE}")
endif()

file(GLOB_RECURSE KERNEL_SOURCES
  src-kernel/*.c
  src-uland/*.c
  libos/*.c
)

add_executable(kernel ${KERNEL_SOURCES})

set(CPUFLAGS "" CACHE STRING "Additional CPU specific compile flags")

target_include_directories(kernel PRIVATE
  ${CMAKE_SOURCE_DIR}
  ${CMAKE_SOURCE_DIR}/src-headers
  ${CMAKE_SOURCE_DIR}/src-kernel/include
  ${CMAKE_SOURCE_DIR}/proto
)

if(CPUFLAGS)
  target_compile_options(kernel PRIVATE ${CPUFLAGS})
endif()

target_link_libraries(kernel PRIVATE nstr_graph)

add_subdirectory(libnstr_graph)

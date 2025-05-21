cmake_minimum_required(VERSION 3.16)
project(xv6 C)

set(CMAKE_C_STANDARD 23)
set(CMAKE_C_COMPILER clang)

include_directories(src-headers src-kernel src-uland)

file(GLOB KERNEL_SRC
     src-kernel/*.c
     src-kernel/exo/*.c
     src-kernel/kernel/*.c)
add_library(kernel_obj OBJECT ${KERNEL_SRC})

file(GLOB ULAND_SRC
     src-uland/*.c
     src-uland/user/*.c)
add_library(ulib_obj OBJECT ${ULAND_SRC})

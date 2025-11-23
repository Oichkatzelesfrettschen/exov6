add_library(libos STATIC
    entry.S
    syscall.c
    umalloc.c
    libmain.c
    fork.c
)
target_include_directories(libos PRIVATE ${CMAKE_SOURCE_DIR}/include)

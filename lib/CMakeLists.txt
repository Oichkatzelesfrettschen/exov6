add_library(libos STATIC
    entry.S
    syscall.c
    umalloc.c
    libmain.c
    fork.c
    print.c
)
target_include_directories(libos PRIVATE ${CMAKE_SOURCE_DIR}/include)

# Disable stack protector for freestanding environment (no libc)
target_compile_options(libos PRIVATE -fno-stack-protector -ffreestanding)

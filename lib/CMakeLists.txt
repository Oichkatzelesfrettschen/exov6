add_library(libos STATIC
    entry.S
    syscall.c
    umalloc.c
    libmain.c
    fork.c
    print.c
    exception.S
    exception.c
    thread_switch.S
    scheduler.c
    fs_client.c
    spawn.c
    fd.c
)
target_include_directories(libos PRIVATE ${CMAKE_SOURCE_DIR}/include)

# Disable stack protector for freestanding environment (no libc)
target_compile_options(libos PRIVATE -fno-stack-protector -ffreestanding)

# DDEKit - Device Driver Environment Kit (LibOS Port)
add_subdirectory(ddekit)

# VirtIO Block Driver Library (Phase 8)
add_subdirectory(virtio)

# File System Library (Phase 8)
add_subdirectory(fs)

# ELF Loader Library (Phase 10)
add_subdirectory(elf)

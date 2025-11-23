# lib/elf/CMakeLists.txt - ELF Loader Library (Phase 10)
#
# EXOKERNEL PHILOSOPHY:
#   The kernel knows NOTHING about ELF format.
#   This library runs entirely in user space (LibOS).

add_library(elf STATIC
    elf_loader.c
)

target_include_directories(elf PUBLIC
    ${CMAKE_CURRENT_SOURCE_DIR}
    ${CMAKE_SOURCE_DIR}/include
)

# Freestanding environment
target_compile_options(elf PRIVATE
    -fno-stack-protector
    -ffreestanding
)

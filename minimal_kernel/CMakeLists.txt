cmake_minimum_required(VERSION 3.20)
project(MinimalKernel LANGUAGES C ASM)

# Force x86_64 target
set(CMAKE_SYSTEM_NAME Generic)
set(CMAKE_SYSTEM_PROCESSOR x86_64)

# Assembly and C flags for freestanding environment
set(CMAKE_ASM_FLAGS "-m32")
set(CMAKE_C_FLAGS "-m32 -ffreestanding -fno-builtin -nostdlib -Wall")

# Boot sector
add_custom_command(
    OUTPUT boot.bin
    COMMAND ${CMAKE_ASM_COMPILER} -o boot.o ${CMAKE_CURRENT_SOURCE_DIR}/boot.S
    COMMAND ld -m elf_i386 --oformat binary -Ttext 0x7c00 -o boot.bin boot.o
    DEPENDS boot.S
)

# Kernel
add_executable(kernel.elf kernel.c)
target_compile_options(kernel.elf PRIVATE -m32 -ffreestanding -fno-builtin -nostdlib)
target_link_options(kernel.elf PRIVATE 
    -m32 -nostdlib -Ttext 0x10000 -e kernel_main
)

# Create disk image
add_custom_command(
    OUTPUT disk.img
    COMMAND dd if=/dev/zero of=disk.img bs=512 count=2880
    COMMAND dd if=boot.bin of=disk.img conv=notrunc
    COMMAND dd if=kernel.elf of=disk.img seek=1 conv=notrunc
    DEPENDS boot.bin kernel.elf
)

add_custom_target(image ALL DEPENDS disk.img)

# QEMU targets
add_custom_target(qemu
    COMMAND qemu-system-i386 -drive file=disk.img,format=raw -nographic
    DEPENDS disk.img
)

add_custom_target(qemu-gui
    COMMAND qemu-system-i386 -drive file=disk.img,format=raw
    DEPENDS disk.img
)
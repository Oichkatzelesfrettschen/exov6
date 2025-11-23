# lib/virtio/CMakeLists.txt
# VirtIO Block Driver Library (Phase 8)

add_library(virtio STATIC virtio.c)

target_include_directories(virtio PUBLIC
    ${CMAKE_CURRENT_SOURCE_DIR}
    ${CMAKE_SOURCE_DIR}/include
)

target_compile_options(virtio PRIVATE
    -fno-stack-protector
    -ffreestanding
    -Wall
    -Wextra
)

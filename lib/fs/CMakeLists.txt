# lib/fs/CMakeLists.txt
# User-Space File System Library (Phase 8)

add_library(fs STATIC
    bio.c
    fs.c
)

target_include_directories(fs PUBLIC
    ${CMAKE_CURRENT_SOURCE_DIR}
    ${CMAKE_CURRENT_SOURCE_DIR}/include
    ${CMAKE_SOURCE_DIR}/include
    ${CMAKE_SOURCE_DIR}/lib/virtio
)

target_link_libraries(fs virtio)

target_compile_options(fs PRIVATE
    -fno-stack-protector
    -ffreestanding
    -Wall
    -Wextra
)

# lib/ddekit/CMakeLists.txt - Device Driver Environment Kit (LibOS Port)
#
# This is the user-space DDEKit that uses Exokernel primitives.
# It provides a device driver abstraction layer for user-space drivers.

# DDEKit sources
set(DDEKIT_SOURCES
    ddekit_backend.c
    stub.c
)

# Optional: badgerferret PCI support
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/badgerferret" AND EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/badgerferret/pci.c")
    list(APPEND DDEKIT_SOURCES badgerferret/pci.c)
endif()

# Create DDEKit library (exokernel primitives version)
# Note: phoenix-libos-ddekit in libos/ddekit is the full-featured version
# This is the minimal version using raw exokernel syscalls
add_library(ddekit-exo STATIC ${DDEKIT_SOURCES})

target_include_directories(ddekit-exo
    PUBLIC
        ${CMAKE_CURRENT_SOURCE_DIR}
        ${CMAKE_SOURCE_DIR}/include
)

# Disable stack protector (freestanding environment)
target_compile_options(ddekit-exo PRIVATE -fno-stack-protector -ffreestanding)

# Link against the core LibOS for syscall wrappers
target_link_libraries(ddekit-exo PUBLIC libos)

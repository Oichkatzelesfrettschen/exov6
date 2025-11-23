# user/CMakeLists.txt (Phase 3 Reconstruction)

# Init process (The First Contractor)
add_executable(init init.c)
target_link_libraries(init libos)
target_include_directories(init PRIVATE ${CMAKE_SOURCE_DIR}/include)

# Disable stack protector for freestanding environment
target_compile_options(init PRIVATE -fno-stack-protector -ffreestanding)

# Link settings for flat binary output
if(APPLE)
    # macOS/Darwin linker uses different flags
    # -e _start sets the entry point
    # -pagezero_size 0 removes the default pagezero segment
    # -image_base sets the base address
    set_target_properties(init PROPERTIES
        LINK_FLAGS "-nostdlib -static -Wl,-e,_start -Wl,-pagezero_size,0 -Wl,-image_base,0x4000 -fno-stack-protector"
    )
else()
    # Linux/ELF linker
    set_target_properties(init PROPERTIES
        LINK_FLAGS "-nostdlib -static -Wl,-Ttext=0x0 -fno-stack-protector"
    )
endif()

# Find objcopy (from binutils or llvm)
find_program(OBJCOPY_EXECUTABLE
    NAMES llvm-objcopy gobjcopy objcopy
    PATHS /opt/homebrew/bin /opt/homebrew/opt/binutils/bin /usr/local/bin /usr/bin
    PATH_SUFFIXES bin
)

if(NOT OBJCOPY_EXECUTABLE)
    # Fallback: try Homebrew binutils directly
    set(OBJCOPY_EXECUTABLE "/opt/homebrew/opt/binutils/bin/objcopy")
endif()

message(STATUS "Using objcopy: ${OBJCOPY_EXECUTABLE}")

# Convert init ELF to flat binary for kernel embedding
add_custom_command(
    OUTPUT ${CMAKE_CURRENT_BINARY_DIR}/init.bin
    COMMAND ${OBJCOPY_EXECUTABLE} -S -O binary $<TARGET_FILE:init> ${CMAKE_CURRENT_BINARY_DIR}/init.bin
    DEPENDS init
    COMMENT "Creating flat binary init.bin for kernel embedding"
)

# Create a custom target for the binary
add_custom_target(init_bin ALL DEPENDS ${CMAKE_CURRENT_BINARY_DIR}/init.bin)

# Export the init.bin path for kernel to use
set(INIT_BIN_PATH ${CMAKE_CURRENT_BINARY_DIR}/init.bin PARENT_SCOPE)

# ═══════════════════════════════════════════════════════════════════════════
# UART Driver - User-Space Hardware Access Test (Phase 5)
# ═══════════════════════════════════════════════════════════════════════════
add_executable(uart_driver uart_driver.c)
target_link_libraries(uart_driver libos)
target_include_directories(uart_driver PRIVATE ${CMAKE_SOURCE_DIR}/include)
target_compile_options(uart_driver PRIVATE -fno-stack-protector -ffreestanding)

if(APPLE)
    set_target_properties(uart_driver PROPERTIES
        LINK_FLAGS "-nostdlib -static -Wl,-e,_start -Wl,-pagezero_size,0 -Wl,-image_base,0x4000 -fno-stack-protector"
    )
else()
    set_target_properties(uart_driver PROPERTIES
        LINK_FLAGS "-nostdlib -static -Wl,-Ttext=0x0 -fno-stack-protector"
    )
endif()

# ═══════════════════════════════════════════════════════════════════════════
# Scheduler Test - Preemptive Scheduling Verification (Phase 6b)
# ═══════════════════════════════════════════════════════════════════════════
add_executable(sched_test sched_test.c)
target_link_libraries(sched_test libos)
target_include_directories(sched_test PRIVATE ${CMAKE_SOURCE_DIR}/include)
target_compile_options(sched_test PRIVATE -fno-stack-protector -ffreestanding)

if(APPLE)
    set_target_properties(sched_test PROPERTIES
        LINK_FLAGS "-nostdlib -static -Wl,-e,_start -Wl,-pagezero_size,0 -Wl,-image_base,0x4000 -fno-stack-protector"
    )
else()
    set_target_properties(sched_test PROPERTIES
        LINK_FLAGS "-nostdlib -static -Wl,-Ttext=0x0 -fno-stack-protector"
    )
endif()

# ═══════════════════════════════════════════════════════════════════════════
# VirtIO Block Driver - User-Space Disk Access (Phase 7)
# ═══════════════════════════════════════════════════════════════════════════
add_executable(virtio_driver virtio_driver.c)
target_link_libraries(virtio_driver libos)
target_include_directories(virtio_driver PRIVATE ${CMAKE_SOURCE_DIR}/include)
target_compile_options(virtio_driver PRIVATE -fno-stack-protector -ffreestanding)

if(APPLE)
    set_target_properties(virtio_driver PROPERTIES
        LINK_FLAGS "-nostdlib -static -Wl,-e,_start -Wl,-pagezero_size,0 -Wl,-image_base,0x4000 -fno-stack-protector"
    )
else()
    set_target_properties(virtio_driver PROPERTIES
        LINK_FLAGS "-nostdlib -static -Wl,-Ttext=0x0 -fno-stack-protector"
    )
endif()

# ═══════════════════════════════════════════════════════════════════════════
# IPC Test - Inter-Process Communication (Phase 9)
# ═══════════════════════════════════════════════════════════════════════════
add_executable(ipc_test ipc_test.c)
target_link_libraries(ipc_test libos)
target_include_directories(ipc_test PRIVATE ${CMAKE_SOURCE_DIR}/include)
target_compile_options(ipc_test PRIVATE -fno-stack-protector -ffreestanding)

if(APPLE)
    set_target_properties(ipc_test PROPERTIES
        LINK_FLAGS "-nostdlib -static -Wl,-e,_start -Wl,-pagezero_size,0 -Wl,-image_base,0x4000 -fno-stack-protector"
    )
else()
    set_target_properties(ipc_test PROPERTIES
        LINK_FLAGS "-nostdlib -static -Wl,-Ttext=0x0 -fno-stack-protector"
    )
endif()

# ═══════════════════════════════════════════════════════════════════════════
# File System Test - User-Space FS (Phase 8)
# ═══════════════════════════════════════════════════════════════════════════
add_executable(fs_test fs_test.c)
target_link_libraries(fs_test libos fs virtio)
target_include_directories(fs_test PRIVATE
    ${CMAKE_SOURCE_DIR}/include
    ${CMAKE_SOURCE_DIR}/lib/virtio
    ${CMAKE_SOURCE_DIR}/lib/fs/include
)
target_compile_options(fs_test PRIVATE -fno-stack-protector -ffreestanding)

if(APPLE)
    set_target_properties(fs_test PROPERTIES
        LINK_FLAGS "-nostdlib -static -Wl,-e,_start -Wl,-pagezero_size,0 -Wl,-image_base,0x4000 -fno-stack-protector"
    )
else()
    set_target_properties(fs_test PROPERTIES
        LINK_FLAGS "-nostdlib -static -Wl,-Ttext=0x0 -fno-stack-protector"
    )
endif()

# Install to bin
install(TARGETS init uart_driver sched_test virtio_driver ipc_test fs_test RUNTIME DESTINATION bin)

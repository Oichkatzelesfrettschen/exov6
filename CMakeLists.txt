cmake_minimum_required(VERSION 3.20)
project(FeuerBird VERSION 1.0.0 LANGUAGES C ASM)

# C17 standard (POSIX-2024 compliance) - STRICT ENFORCEMENT
set(CMAKE_C_STANDARD 17)
set(CMAKE_C_STANDARD_REQUIRED ON)
set(CMAKE_C_EXTENSIONS OFF)  # NO GNU extensions - pure C17 only

# Verify C17 compiler support
include(CheckCSourceCompiles)
check_c_source_compiles("
    #include <stdatomic.h>
    #include <threads.h>
    #include <stdalign.h>
    int main() { 
        _Atomic(int) x = 0; 
        _Static_assert(1, \"C17 required\");
        _Alignas(64) char buf[64];
        return 0; 
    }
" HAS_FULL_C17_SUPPORT)

if(NOT HAS_FULL_C17_SUPPORT)
    message(FATAL_ERROR "Full C17 support is required. Please use a modern compiler (Clang 15+ or GCC 11+)")
endif()

# Native x86_64 build
set(ARCH "x86_64" CACHE STRING "Target architecture")
set(CMAKE_SYSTEM_PROCESSOR ${ARCH})

# Force x86_64 definitions
add_definitions(-D__x86_64__ -D__LP64__)

# Enable legacy types during migration
add_definitions(-DLEGACY_TYPES_COMPATIBILITY)

# Cross-compilation from ARM64 to x86_64
if(CMAKE_HOST_SYSTEM_PROCESSOR MATCHES "arm64|aarch64")
    set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} -target x86_64-unknown-none-elf")
    set(CMAKE_ASM_FLAGS "${CMAKE_ASM_FLAGS} -target x86_64-unknown-none-elf")
endif()

# C17 strict compiler flags
set(C17_STRICT_FLAGS 
    -std=c17
    -Wpedantic
    -Wvla  # No variable-length arrays
    -Wno-gnu-zero-variadic-macro-arguments
    -D_POSIX_C_SOURCE=202405L  # POSIX-2024
)

# Default compiler flags for host tools
set(HOST_COMPILE_FLAGS -Wall -Wextra -O2 ${C17_STRICT_FLAGS})

# Kernel-specific compiler flags (freestanding environment)
set(KERNEL_COMPILE_FLAGS
    -ffreestanding
    -fno-builtin
    -fno-stack-protector
    -fno-omit-frame-pointer
    -nostdlib
    -mcmodel=kernel
    -mno-red-zone
    -mno-sse
    -Wall -Wextra
    -target x86_64-unknown-none-elf
    ${C17_STRICT_FLAGS}
)

# Debug/Release
if(CMAKE_BUILD_TYPE STREQUAL "Debug")
    add_compile_options(-O0 -g3 -DDEBUG)
else()
    add_compile_options(-O3 -DNDEBUG)
endif()

# ============================================================================
# Build Output Directory Configuration (Best Practices)
# ============================================================================

# Enforce out-of-source builds
if(CMAKE_SOURCE_DIR STREQUAL CMAKE_BINARY_DIR)
    message(FATAL_ERROR "In-source builds are not allowed. Please create a build directory.")
endif()

# Set output directories for different artifact types
set(CMAKE_ARCHIVE_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/lib)
set(CMAKE_LIBRARY_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/lib)
set(CMAKE_RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/bin)

# Per-configuration output directories (for multi-config generators)
foreach(CONFIG ${CMAKE_CONFIGURATION_TYPES})
    string(TOUPPER ${CONFIG} CONFIG_UPPER)
    set(CMAKE_ARCHIVE_OUTPUT_DIRECTORY_${CONFIG_UPPER} ${CMAKE_BINARY_DIR}/${CONFIG}/lib)
    set(CMAKE_LIBRARY_OUTPUT_DIRECTORY_${CONFIG_UPPER} ${CMAKE_BINARY_DIR}/${CONFIG}/lib)
    set(CMAKE_RUNTIME_OUTPUT_DIRECTORY_${CONFIG_UPPER} ${CMAKE_BINARY_DIR}/${CONFIG}/bin)
endforeach()

# Object file directories for intermediate build artifacts
set(CMAKE_OBJECT_PATH_PREFIX ${CMAKE_BINARY_DIR}/obj/)

# Include directories will be set per target
# No global includes to avoid host/target conflicts

# ============================================================================
# Kernel Components (Organized by Subsystem)
# ============================================================================

# Boot subsystem
set(KERNEL_BOOT_SOURCES
    kernel/boot/bootmain.c
    kernel/boot/main.c
    kernel/boot/main64.c
    kernel/boot/bootasm.S
    kernel/boot/entry.S
    kernel/initcode.S
    kernel/entryother.S
)

# Memory subsystem
set(KERNEL_MEM_SOURCES
    kernel/mem/vm.c
    kernel/mem/kalloc.c
    kernel/mem/mmu64.c
    kernel/mem/libbaremetal.c
)

# File system subsystem
set(KERNEL_FS_SOURCES
    kernel/fs/fs.c
    kernel/fs/bio.c
    kernel/fs/log.c
    kernel/fs/ide.c
)

# IPC subsystem
set(KERNEL_IPC_SOURCES
    kernel/ipc/cap.c
    kernel/ipc/cap_table.c
    kernel/ipc/cap_mem.c
    kernel/ipc/capnp_helpers.c
    kernel/ipc/capwrap.c
    kernel/ipc/chan.c
    kernel/ipc/endpoint.c
    kernel/ipc/exo.c
    kernel/ipc/exo_cpu.c
    kernel/ipc/exo_disk.c
    kernel/ipc/exo_ipc.c
    kernel/ipc/exo_ipc_queue.c
    kernel/ipc/exo_stream.c
    kernel/ipc/fastipc.c
    kernel/ipc/lattice_ipc.c
    kernel/ipc/sys_ipc.c
)

# Scheduling subsystem
set(KERNEL_SCHED_SOURCES
    kernel/sched/proc.c
    kernel/sched/beatty_sched.c
    kernel/sched/dag_sched.c
    kernel/sched/beatty_dag_stream.c
)

# Synchronization subsystem
set(KERNEL_SYNC_SOURCES
    kernel/sync/spinlock.c      # Primary ticket spinlock implementation
    kernel/sync/sleeplock.c     # Sleeping locks
    kernel/sync/rcu.c           # Read-Copy-Update
    kernel/sync/modern_locks.c  # MCS, CLH, and advanced locks
)

# System call subsystem
set(KERNEL_SYS_SOURCES
    kernel/sys/syscall.c
    kernel/sys/sysproc.c
    kernel/sys/sysfile.c
    kernel/sys/trap.c
    kernel/sys/trapasm.S
    kernel/sys/exec.c
    kernel/sys/pipe.c
    kernel/sys/string.c
    kernel/swtch.S
    kernel/swtch64.S
)

# Driver subsystem
set(KERNEL_DRIVER_SOURCES
    kernel/drivers/console.c
    kernel/drivers/uart.c
    kernel/drivers/kbd.c
    kernel/drivers/ioapic.c
    kernel/drivers/lapic.c
    kernel/drivers/picirq.c
    kernel/drivers/mp.c
    kernel/drivers/ddekit.c
    kernel/drivers/driver.c
    kernel/drivers/iommu.c
    kernel/drivers/memide.c
)

# Hypervisor subsystem
set(KERNEL_HYPERVISOR_SOURCES
    kernel/hypervisor/hypervisor.c
)

# Core kernel files
set(KERNEL_CORE_SOURCES
    kernel/arbitrate.c
    kernel/crypto.c
    kernel/env.c
    kernel/irq.c
    kernel/lambda_cap.c
    kernel/lib9p.c
    kernel/memutil.c
    kernel/msg_router.c
    kernel/octonion.c
    kernel/picokernel.c
    kernel/registration.c
    kernel/resource_account.c
    kernel/service.c
    kernel/streams.c
    kernel/tty.c
    kernel/zone.c
    kernel/zone_isolation.c
)

# Combine all kernel sources
set(KERNEL_SOURCES
    ${KERNEL_BOOT_SOURCES}
    ${KERNEL_MEM_SOURCES}
    ${KERNEL_FS_SOURCES}
    ${KERNEL_IPC_SOURCES}
    ${KERNEL_SCHED_SOURCES}
    ${KERNEL_SYNC_SOURCES}
    ${KERNEL_SYS_SOURCES}
    ${KERNEL_DRIVER_SOURCES}
    ${KERNEL_HYPERVISOR_SOURCES}
    ${KERNEL_CORE_SOURCES}
)

# ============================================================================
# LibOS Components (Organized by Function)
# ============================================================================

# POSIX layer
set(LIBOS_POSIX_SOURCES
    libos/posix/posix.c
)

# Threading
set(LIBOS_PTHREAD_SOURCES
    libos/pthread/pthread_core.c
    libos/pthread/pthread_mutex.c
)

# Signal handling
set(LIBOS_SIGNAL_SOURCES
    libos/signal/signal_posix.c
)

# File system
set(LIBOS_FS_SOURCES
    libos/fs/fs.c
    libos/fs/fs_ext.c
    libos/fs/file.c
    libos/libfs_stubs.c
)

# Memory management
set(LIBOS_MEM_SOURCES
    libos/mem/memory.c
)

# Core libos files
set(LIBOS_CORE_SOURCES
    libos/affine_runtime.c
    libos/cap.c
    libos/capnp_helpers.c
    libos/capwrap.c
    libos/env.c
    libos/errno.c
    libos/ipc.c
    libos/ipc_queue.c
    libos/irq_client.c
    libos/lambda_cap.c
    libos/msg_router.c
    libos/process.c
    libos/procwrap.c
    libos/registration.c
    libos/resource_account.c
    libos/sched.c
    libos/sched_helpers.c
    libos/service.c
    libos/termios.c
    libos/time.c
    libos/user.c
)

# Combine all libos sources
set(LIBOS_SOURCES
    ${LIBOS_POSIX_SOURCES}
    ${LIBOS_PTHREAD_SOURCES}
    ${LIBOS_SIGNAL_SOURCES}
    ${LIBOS_FS_SOURCES}
    ${LIBOS_MEM_SOURCES}
    ${LIBOS_CORE_SOURCES}
)

# ============================================================================
# User Programs (Deduplicated)
# ============================================================================

set(USER_CORE_UTILS
    cat echo grep ls mkdir rm wc cp mv pwd
)

set(USER_FILE_UTILS
    chmod chown ln touch dd df du
)

set(USER_PROCESS_UTILS
    ps kill nice renice
)

set(USER_SHELL_UTILS
    sh test true false
)

set(USER_SYSTEM_UTILS
    init date uname whoami hostname
)

set(USER_PROGRAMS
    ${USER_CORE_UTILS}
    ${USER_FILE_UTILS}
    ${USER_PROCESS_UTILS}
    ${USER_SHELL_UTILS}
    ${USER_SYSTEM_UTILS}
)

# Build user programs
foreach(prog ${USER_PROGRAMS})
    if(EXISTS ${CMAKE_CURRENT_SOURCE_DIR}/user/${prog}.c)
        add_executable(_${prog} 
            user/${prog}.c 
            user/ulib.c 
            user/printf.c
            user/umalloc.c
            user/usys.S
        )
        target_link_libraries(_${prog} libos)
        set_target_properties(_${prog} PROPERTIES
            LINK_FLAGS "-N -e main"
            RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/fs/bin
        )
    endif()
endforeach()

# ============================================================================
# Libraries
# ============================================================================

# Kernel library (freestanding)
add_library(kernel STATIC ${KERNEL_SOURCES})
target_compile_options(kernel PRIVATE ${KERNEL_COMPILE_FLAGS})
target_include_directories(kernel PRIVATE
    ${CMAKE_SOURCE_DIR}/include
    ${CMAKE_SOURCE_DIR}/kernel
)

# LibOS library (also freestanding)
add_library(libos STATIC ${LIBOS_SOURCES})
target_compile_options(libos PRIVATE ${KERNEL_COMPILE_FLAGS})
target_include_directories(libos PRIVATE
    ${CMAKE_SOURCE_DIR}/include
    ${CMAKE_SOURCE_DIR}/libos
)

# ============================================================================
# Tools
# ============================================================================

# Host tool: mkfs (built with host compiler, NO kernel headers)
add_executable(mkfs tools/mkfs.c)
target_compile_options(mkfs PRIVATE ${HOST_COMPILE_FLAGS})
# Do NOT include our headers for host tools - use system headers only
target_include_directories(mkfs PRIVATE)
set_target_properties(mkfs PROPERTIES
    RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/bin/tools
)

# ============================================================================
# Kernel Image
# ============================================================================

# Bootblock
add_custom_command(
    OUTPUT bootblock
    COMMAND ${CMAKE_C_COMPILER} -fno-pic -O -nostdinc -I${CMAKE_SOURCE_DIR}/include 
            -c ${CMAKE_SOURCE_DIR}/kernel/boot/bootmain.c
    COMMAND ${CMAKE_C_COMPILER} -fno-pic -nostdinc -I${CMAKE_SOURCE_DIR}/include 
            -c ${CMAKE_SOURCE_DIR}/kernel/boot/bootasm.S
    COMMAND ld -m elf_x86_64 -N -e start -Ttext 0x7C00 -o bootblock.o bootasm.o bootmain.o
    COMMAND objcopy -S -O binary -j .text bootblock.o bootblock
    DEPENDS kernel/boot/bootmain.c kernel/boot/bootasm.S
)

# Kernel executable (freestanding)
add_executable(kernel.elf ${KERNEL_SOURCES})
target_compile_options(kernel.elf PRIVATE ${KERNEL_COMPILE_FLAGS})
target_include_directories(kernel.elf PRIVATE
    ${CMAKE_SOURCE_DIR}/include
    ${CMAKE_SOURCE_DIR}/kernel
)
target_link_options(kernel.elf PRIVATE
    -T ${CMAKE_SOURCE_DIR}/kernel.ld
    -nostdlib
    -static
)
set_target_properties(kernel.elf PROPERTIES
    RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/bin
)

# File system image
add_custom_command(
    OUTPUT fs.img
    COMMAND ${CMAKE_BINARY_DIR}/bin/tools/mkfs fs.img ${CMAKE_SOURCE_DIR}/README.md ${USER_PROGRAMS}
    DEPENDS mkfs ${USER_PROGRAMS}
    WORKING_DIRECTORY ${CMAKE_BINARY_DIR}/fs/bin
)

# OS image
add_custom_command(
    OUTPUT xv6.img
    COMMAND dd if=/dev/zero of=xv6.img count=10000 2>/dev/null
    COMMAND dd if=bootblock of=xv6.img conv=notrunc 2>/dev/null
    COMMAND dd if=kernel.elf of=xv6.img seek=1 conv=notrunc 2>/dev/null
    DEPENDS bootblock kernel.elf
)

# ============================================================================
# Demo Programs
# ============================================================================

set(DEMO_PROGRAMS
    beatty_demo
    dag_demo
    chan_demo
    ipc_demo
    capability_demo
    posix_test
)

foreach(demo ${DEMO_PROGRAMS})
    if(EXISTS ${CMAKE_CURRENT_SOURCE_DIR}/demos/${demo}.c)
        add_executable(demo_${demo} demos/${demo}.c)
        target_link_libraries(demo_${demo} libos)
        set_target_properties(demo_${demo} PROPERTIES
            RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/bin/demos
        )
    endif()
endforeach()

# ============================================================================
# Tests
# ============================================================================

enable_testing()

# Tests will be added as they are created
# For now, we have the Python test suite

# Python tests
add_test(NAME pytest_suite 
    COMMAND python3 -m pytest -v tests/
    WORKING_DIRECTORY ${CMAKE_SOURCE_DIR}
)

# ============================================================================
# QEMU Targets
# ============================================================================

set(QEMU_OPTIONS
    -serial mon:stdio
    -drive file=fs.img,index=1,media=disk,format=raw
    -drive file=xv6.img,index=0,media=disk,format=raw
    -smp 2 -m 512
)

add_custom_target(qemu
    COMMAND qemu-system-x86_64 ${QEMU_OPTIONS}
    DEPENDS xv6.img fs.img
    COMMENT "Running in QEMU"
)

add_custom_target(qemu-nox
    COMMAND qemu-system-x86_64 -nographic ${QEMU_OPTIONS}
    DEPENDS xv6.img fs.img
    COMMENT "Running in QEMU (no graphics)"
)

add_custom_target(qemu-gdb
    COMMAND qemu-system-x86_64 ${QEMU_OPTIONS} -S -gdb tcp::26000
    DEPENDS xv6.img fs.img
    COMMENT "Running in QEMU with GDB"
)

# ============================================================================
# Code Quality
# ============================================================================

# Get all source files
file(GLOB_RECURSE ALL_SOURCES 
    ${CMAKE_SOURCE_DIR}/kernel/*.c
    ${CMAKE_SOURCE_DIR}/libos/*.c
    ${CMAKE_SOURCE_DIR}/user/*.c
    ${CMAKE_SOURCE_DIR}/include/*.h
)

add_custom_target(format
    COMMAND clang-format -i -style=LLVM ${ALL_SOURCES}
    COMMENT "Formatting code"
)

add_custom_target(lint
    COMMAND clang-tidy ${ALL_SOURCES} -- -std=c17 -I${CMAKE_SOURCE_DIR}/include
    COMMENT "Running linter"
)

add_custom_target(analyze
    COMMAND scan-build cmake --build ${CMAKE_BINARY_DIR}
    WORKING_DIRECTORY ${CMAKE_BINARY_DIR}
    COMMENT "Running static analysis"
)

# ============================================================================
# Installation
# ============================================================================

install(TARGETS kernel.elf DESTINATION bin)
install(FILES fs.img xv6.img DESTINATION share/feuerbird)
install(DIRECTORY include/ DESTINATION include/feuerbird)

# ============================================================================
# Documentation
# ============================================================================

find_package(Doxygen)
if(DOXYGEN_FOUND)
    add_custom_target(docs
        COMMAND ${DOXYGEN_EXECUTABLE} ${CMAKE_SOURCE_DIR}/docs/Doxyfile
        WORKING_DIRECTORY ${CMAKE_SOURCE_DIR}
        COMMENT "Generating API documentation (see README.md for complete project documentation)"
    )
endif()

# Print configuration
message(STATUS "=========================================")
message(STATUS "FeuerBird Configuration (Reorganized)")
message(STATUS "=========================================")
message(STATUS "Architecture: ${ARCH}")
message(STATUS "Compiler: ${CMAKE_C_COMPILER}")
message(STATUS "Build Type: ${CMAKE_BUILD_TYPE}")
message(STATUS "Kernel sources: ${KERNEL_SOURCES}")
message(STATUS "LibOS sources: ${LIBOS_SOURCES}")
message(STATUS "User programs: ${USER_PROGRAMS}")
message(STATUS "=========================================")
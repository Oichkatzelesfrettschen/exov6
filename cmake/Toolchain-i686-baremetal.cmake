# cmake/Toolchain-i686-baremetal.cmake
# Cross-compilation toolchain for 32-bit bare-metal FeuerBird kernel
#
# Usage: cmake -DCMAKE_TOOLCHAIN_FILE=cmake/Toolchain-i686-baremetal.cmake ..

set(CMAKE_SYSTEM_NAME Generic)
set(CMAKE_SYSTEM_PROCESSOR i686)

# Use clang with explicit 32-bit target
set(CMAKE_C_COMPILER clang)
set(CMAKE_CXX_COMPILER clang++)
set(CMAKE_ASM_COMPILER clang)

# Target triple for bare-metal i686
set(FEUERBIRD_TARGET_TRIPLE "i686-elf")

# Freestanding compilation flags (no libc, no standard libraries)
set(CMAKE_C_FLAGS_INIT
    "-target i686-elf \
     -m32 \
     -ffreestanding \
     -fno-stack-protector \
     -fno-pie \
     -fno-pic \
     -mno-red-zone \
     -fno-builtin \
     -nostdlib \
     -Wall -Wextra"
)

set(CMAKE_CXX_FLAGS_INIT
    "-target i686-elf \
     -m32 \
     -ffreestanding \
     -fno-stack-protector \
     -fno-pie \
     -fno-pic \
     -mno-red-zone \
     -fno-builtin \
     -nostdlib \
     -fno-exceptions \
     -fno-rtti \
     -Wall -Wextra"
)

set(CMAKE_ASM_FLAGS_INIT
    "-target i686-elf \
     -m32"
)

# Linker flags for bare-metal
set(CMAKE_EXE_LINKER_FLAGS_INIT
    "-nostdlib \
     -static \
     -fuse-ld=lld"
)

# Disable standard library lookup
set(CMAKE_C_STANDARD_LIBRARIES "")
set(CMAKE_CXX_STANDARD_LIBRARIES "")

# Skip compiler checks that require running binaries
set(CMAKE_C_COMPILER_WORKS 1)
set(CMAKE_CXX_COMPILER_WORKS 1)
set(CMAKE_TRY_COMPILE_TARGET_TYPE STATIC_LIBRARY)

# Mark this as a cross-compilation
set(CMAKE_CROSSCOMPILING TRUE)

# Indicate kernel build mode
set(FEUERBIRD_KERNEL_BUILD TRUE CACHE BOOL "Building bare-metal kernel")
set(FEUERBIRD_ARCH "i686" CACHE STRING "Target architecture")

message(STATUS "FeuerBird Toolchain: i686 bare-metal kernel")
message(STATUS "  Target: ${FEUERBIRD_TARGET_TRIPLE}")
message(STATUS "  Compiler: ${CMAKE_C_COMPILER}")

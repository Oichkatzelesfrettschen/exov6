# Cross-compilation toolchain file for x86_64 target from ARM64 host
# Usage: cmake -DCMAKE_TOOLCHAIN_FILE=toolchain-x86_64.cmake ..

set(CMAKE_SYSTEM_NAME Generic)
set(CMAKE_SYSTEM_PROCESSOR x86_64)

# Target triple for cross-compilation
set(TARGET_TRIPLE x86_64-unknown-none-elf)

# Use host clang for cross-compilation (it's a cross-compiler)
set(CMAKE_C_COMPILER clang)
set(CMAKE_CXX_COMPILER clang++)
set(CMAKE_ASM_COMPILER clang)

# Tell CMake this is cross-compilation
set(CMAKE_CROSSCOMPILING TRUE)

# Compiler flags for cross-compilation
set(CMAKE_C_FLAGS_INIT "-target ${TARGET_TRIPLE}")
set(CMAKE_CXX_FLAGS_INIT "-target ${TARGET_TRIPLE}")
set(CMAKE_ASM_FLAGS_INIT "-target ${TARGET_TRIPLE}")

# Don't run the linker for compiler tests (we're freestanding)
set(CMAKE_TRY_COMPILE_TARGET_TYPE STATIC_LIBRARY)

# Search for programs in the host environment
set(CMAKE_FIND_ROOT_PATH_MODE_PROGRAM NEVER)

# Search for libraries and headers in the target environment
set(CMAKE_FIND_ROOT_PATH_MODE_LIBRARY ONLY)
set(CMAKE_FIND_ROOT_PATH_MODE_INCLUDE ONLY)
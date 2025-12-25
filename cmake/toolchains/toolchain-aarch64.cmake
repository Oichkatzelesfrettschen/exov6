# Cross-compilation toolchain file for AArch64 target 
# Usage: cmake -DCMAKE_TOOLCHAIN_FILE=toolchain-aarch64.cmake ..

set(CMAKE_SYSTEM_NAME Generic)
set(CMAKE_SYSTEM_PROCESSOR aarch64)

# Target triple for compilation
set(TARGET_TRIPLE aarch64-unknown-none-elf)

# Use host clang for compilation
set(CMAKE_C_COMPILER clang)
set(CMAKE_CXX_COMPILER clang++)
set(CMAKE_ASM_COMPILER clang)

# For native ARM64 on Apple M1, we might not need cross-compilation
if(CMAKE_HOST_SYSTEM_PROCESSOR MATCHES "arm64|aarch64")
    set(CMAKE_CROSSCOMPILING FALSE)
else()
    set(CMAKE_CROSSCOMPILING TRUE)
endif()

# Compiler flags
set(CMAKE_C_FLAGS_INIT "-target ${TARGET_TRIPLE}")
set(CMAKE_CXX_FLAGS_INIT "-target ${TARGET_TRIPLE}")
set(CMAKE_ASM_FLAGS_INIT "-target ${TARGET_TRIPLE}")

# Don't run the linker for compiler tests (we're freestanding)
set(CMAKE_TRY_COMPILE_TARGET_TYPE STATIC_LIBRARY)

# Search paths
set(CMAKE_FIND_ROOT_PATH_MODE_PROGRAM NEVER)
set(CMAKE_FIND_ROOT_PATH_MODE_LIBRARY ONLY)
set(CMAKE_FIND_ROOT_PATH_MODE_INCLUDE ONLY)
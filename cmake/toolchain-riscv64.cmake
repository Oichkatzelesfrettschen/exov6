# Cross-compilation toolchain file for RISC-V 64 target
# Usage: cmake -DCMAKE_TOOLCHAIN_FILE=../cmake/toolchain-riscv64.cmake ..

set(CMAKE_SYSTEM_NAME Generic)
set(CMAKE_SYSTEM_PROCESSOR riscv64)

# Target triple for compilation
set(TARGET_TRIPLE riscv64-unknown-none-elf)

set(CMAKE_C_COMPILER clang)
set(CMAKE_CXX_COMPILER clang++)
set(CMAKE_ASM_COMPILER clang)

set(CMAKE_C_FLAGS_INIT "-target ${TARGET_TRIPLE} -march=rv64gc -mabi=lp64d")
set(CMAKE_CXX_FLAGS_INIT "-target ${TARGET_TRIPLE} -march=rv64gc -mabi=lp64d")
set(CMAKE_ASM_FLAGS_INIT "-target ${TARGET_TRIPLE} -march=rv64gc -mabi=lp64d")

set(CMAKE_TRY_COMPILE_TARGET_TYPE STATIC_LIBRARY)
set(CMAKE_FIND_ROOT_PATH_MODE_PROGRAM NEVER)
set(CMAKE_FIND_ROOT_PATH_MODE_LIBRARY ONLY)
set(CMAKE_FIND_ROOT_PATH_MODE_INCLUDE ONLY)

cmake_minimum_required(VERSION 3.16)

if(NOT DEFINED CMAKE_C_COMPILER)
  set(CMAKE_C_COMPILER clang)
endif()
if(NOT DEFINED CMAKE_CXX_COMPILER)
  set(CMAKE_CXX_COMPILER clang++)
endif()

project(xv6 LANGUAGES C CXX)

# Include required modules
include(CheckCCompilerFlag)

option(USE_TICKET_LOCK "Use ticket-based spinlocks" OFF)
option(IPC_DEBUG "Enable IPC debug logging" OFF)
option(USE_CAPNP "Build Cap'n Proto support" OFF)
option(USE_SIMD "Enable SIMD math routines" OFF)
option(MCU "Build for Cortex-M microcontroller" OFF)
option(USE_LTO "Enable Link Time Optimization" OFF)
option(USE_LLD "Use LLVM LLD linker" OFF)
option(USE_POLLY "Enable LLVM Polly optimizations" OFF)
option(ENABLE_ASAN "Enable AddressSanitizer" OFF)
option(ENABLE_TSAN "Enable ThreadSanitizer" OFF)
option(ENABLE_UBSAN "Enable UndefinedBehaviorSanitizer" OFF)

add_compile_options(-std=c2x)
set(CMAKE_C_STANDARD 23)
set(CMAKE_C_STANDARD_REQUIRED ON)
set(CMAKE_CXX_STANDARD 23)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_EXPORT_COMPILE_COMMANDS ON)
add_compile_options(-Wall -Werror)

# Configure modern LLVM toolchain
if(USE_LLD)
  if(CMAKE_C_COMPILER_ID MATCHES "Clang")
    set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} -fuse-ld=lld")
    set(CMAKE_SHARED_LINKER_FLAGS "${CMAKE_SHARED_LINKER_FLAGS} -fuse-ld=lld")
    message(STATUS "Using LLVM LLD linker")
  else()
    message(WARNING "LLD linker requires Clang compiler")
  endif()
endif()

# Configure LLVM archiver and tools
if(CMAKE_C_COMPILER_ID MATCHES "Clang")
  find_program(LLVM_AR NAMES llvm-ar-18 llvm-ar)
  find_program(LLVM_OBJCOPY NAMES llvm-objcopy-18 llvm-objcopy)
  find_program(LLVM_STRIP NAMES llvm-strip-18 llvm-strip)
  find_program(LLVM_NM NAMES llvm-nm-18 llvm-nm)
  find_program(LLVM_OBJDUMP NAMES llvm-objdump-18 llvm-objdump)
  
  if(LLVM_AR)
    set(CMAKE_AR "${LLVM_AR}")
    message(STATUS "Using LLVM archiver: ${LLVM_AR}")
  endif()
  if(LLVM_OBJCOPY)
    set(CMAKE_OBJCOPY "${LLVM_OBJCOPY}")
  endif()
  if(LLVM_STRIP)
    set(CMAKE_STRIP "${LLVM_STRIP}")
  endif()
endif()

# Configure Link Time Optimization
if(USE_LTO)
  if(CMAKE_C_COMPILER_ID MATCHES "Clang")
    set(CMAKE_INTERPROCEDURAL_OPTIMIZATION ON)
    add_compile_options(-flto=thin)
    add_link_options(-flto=thin)
    message(STATUS "Enabled LLVM ThinLTO")
  else()
    message(WARNING "LTO requires Clang compiler for LLVM ThinLTO")
  endif()
endif()

# Configure Polly optimizations
if(USE_POLLY)
  if(CMAKE_C_COMPILER_ID MATCHES "Clang")
    find_program(OPT_POLLY NAMES opt-18 opt)
    if(OPT_POLLY)
      add_compile_options(-mllvm -polly)
      add_compile_options(-mllvm -polly-vectorizer=stripmine)
      add_compile_options(-mllvm -polly-parallel)
      message(STATUS "Enabled LLVM Polly optimizations")
    else()
      message(WARNING "Polly optimizations require LLVM opt tool")
    endif()
  else()
    message(WARNING "Polly optimizations require Clang compiler")
  endif()
endif()

# Configure sanitizers
if(ENABLE_ASAN)
  add_compile_options(-fsanitize=address -fno-omit-frame-pointer)
  add_link_options(-fsanitize=address)
  message(STATUS "Enabled AddressSanitizer")
endif()

if(ENABLE_TSAN)
  add_compile_options(-fsanitize=thread)
  add_link_options(-fsanitize=thread)
  message(STATUS "Enabled ThreadSanitizer")
endif()

if(ENABLE_UBSAN)
  add_compile_options(-fsanitize=undefined)
  add_link_options(-fsanitize=undefined)
  message(STATUS "Enabled UndefinedBehaviorSanitizer")
endif()

#Enable decimal floating point when supported
check_c_compiler_flag("-mdecimal-float" HAVE_DECIMAL_FLOAT)
if(HAVE_DECIMAL_FLOAT)
  add_compile_options(-mdecimal-float)
  add_compile_definitions(HAVE_DECIMAL_FLOAT=1)
endif()

if(NOT CMAKE_C_COMPILER_ID MATCHES "Clang")
  message(WARNING "Clang is recommended for building this project")
endif()

find_program(CLANG_TIDY_EXE NAMES clang-tidy)
if(CLANG_TIDY_EXE AND NOT DEFINED CMAKE_C_CLANG_TIDY)
  # Only enable clang-tidy if explicitly requested and not conflicting
  # set(CMAKE_C_CLANG_TIDY "${CLANG_TIDY_EXE}")
  message(STATUS "clang-tidy found but disabled due to header conflicts")
endif()

find_package(BISON)
if(BISON_FOUND)
  BISON_TARGET(example_parser
    proto/example.y
    ${CMAKE_CURRENT_BINARY_DIR}/example_parser.c
    DEFINES_FILE ${CMAKE_CURRENT_BINARY_DIR}/example_parser.h)
  add_custom_target(example_bison DEPENDS ${BISON_example_parser_OUTPUTS})
endif()

if(MCU)
  target_include_directories(kernel PRIVATE
    ${CMAKE_SOURCE_DIR}/src
    ${CMAKE_SOURCE_DIR}/src/arch/mcu
    ${CMAKE_SOURCE_DIR}/include)
  add_compile_definitions(MCU=1)
  return()
endif()
file(GLOB_RECURSE KERNEL_SOURCES
  kernel/*.c
)
file(GLOB_RECURSE ARCH_X86_LEGACY_SOURCES src/arch/x86/legacy/*.c)
file(GLOB_RECURSE ARCH_X86_MODERN_SOURCES src/arch/x86/modern/*.c)
list(APPEND KERNEL_SOURCES
  ${ARCH_X86_LEGACY_SOURCES}
  ${ARCH_X86_MODERN_SOURCES})

set(SIMD_SOURCES
  src/arch/simd_dispatch.c
)

if(CMAKE_SYSTEM_PROCESSOR MATCHES "x86_64" OR CMAKE_SYSTEM_PROCESSOR MATCHES "i.86")
  list(APPEND SIMD_SOURCES
    src/arch/x86/simd_x87.c
    src/arch/x86/simd_mmx.c
    src/arch/x86/simd_sse2.c
    src/arch/x86/simd_avx.c
    src/arch/x86/legacy/simd_mmx_cap.c
    src/arch/x86/modern/simd_avx2_cap.c)
  set_source_files_properties(src/arch/x86/simd_mmx.c PROPERTIES COMPILE_OPTIONS "-mmmx")
  set_source_files_properties(src/arch/x86/simd_sse2.c PROPERTIES COMPILE_OPTIONS "-msse2")
  set_source_files_properties(src/arch/x86/simd_avx.c PROPERTIES COMPILE_OPTIONS "-mavx")
  set_source_files_properties(src/arch/x86/legacy/simd_mmx_cap.c PROPERTIES COMPILE_OPTIONS "-mmmx")
  set_source_files_properties(src/arch/x86/modern/simd_avx2_cap.c PROPERTIES COMPILE_OPTIONS "-mavx2")
endif()

if(CMAKE_SYSTEM_PROCESSOR MATCHES "aarch64" OR CMAKE_SYSTEM_PROCESSOR MATCHES "arm")
  list(APPEND SIMD_SOURCES src/arch/arm/simd_neon.c src/arch/arm/simd_neon_cap.c)
  set_source_files_properties(src/arch/arm/simd_neon.c PROPERTIES COMPILE_OPTIONS "-mfpu=neon")
  set_source_files_properties(src/arch/arm/simd_neon_cap.c PROPERTIES COMPILE_OPTIONS "-mfpu=neon")
endif()

if(CMAKE_SYSTEM_PROCESSOR MATCHES "powerpc")
  list(APPEND SIMD_SOURCES src/arch/ppc/simd_altivec.c src/arch/ppc/simd_altivec_cap.c)
  set_source_files_properties(src/arch/ppc/simd_altivec.c PROPERTIES COMPILE_OPTIONS "-maltivec")
  set_source_files_properties(src/arch/ppc/simd_altivec_cap.c PROPERTIES COMPILE_OPTIONS "-maltivec")
endif()

add_library(simd_dispatch STATIC ${SIMD_SOURCES})
target_include_directories(simd_dispatch PUBLIC
  ${CMAKE_SOURCE_DIR}/src
  ${CMAKE_SOURCE_DIR}/tools
)

set(LIBPOSIX_SOURCES libos/stubs/libposix.c)
set(LIBBAREMETAL_SOURCES libos/stubs/libbaremetal.c)
set(LIB9P_SOURCES libos/stubs/lib9p.c)

set(LIBOS_SOURCES
  user/ulib.c
  user/printf.c
  user/umalloc.c
  user/caplib.c
  user/chan.c
  user/door.c
  user/math_core.c
  user/libos/sched.c
  libos/fs.c
  libos/file.c
  libos/affine_runtime.c
  libos/ipc.c
  libos/posix.c
  libos/termios.c
  libos/service.c
  libos/cap.c
  libos/msg_router.c
  libos/resource_account.c
  libos/registration.c
  ${LIBPOSIX_SOURCES}
  ${LIBBAREMETAL_SOURCES}
  ${LIB9P_SOURCES}
)
add_library(libos STATIC ${LIBOS_SOURCES})
target_include_directories(libos PUBLIC
  ${CMAKE_SOURCE_DIR}
  ${CMAKE_SOURCE_DIR}/include
  ${CMAKE_SOURCE_DIR}/proto
  ${CMAKE_SOURCE_DIR}/libos/capnp
  ${CMAKE_SOURCE_DIR}/src
  ${CMAKE_SOURCE_DIR}/src/arch/x86/legacy
  ${CMAKE_SOURCE_DIR}/src/arch/x86/modern
  ${CMAKE_SOURCE_DIR}/libos/stubs
)
target_link_libraries(libos PUBLIC simd_dispatch)
if(USE_SIMD)
  target_compile_definitions(libos PUBLIC USE_SIMD)
endif()

if(USE_CAPNP)
  add_custom_command(
    OUTPUT ${CMAKE_CURRENT_BINARY_DIR}/driver.capnp.c ${CMAKE_CURRENT_BINARY_DIR}/driver.capnp.h
    COMMAND ${CMAKE_SOURCE_DIR}/scripts/mock_capnpc.sh ${CMAKE_SOURCE_DIR}/proto/driver.capnp
    DEPENDS ${CMAKE_SOURCE_DIR}/proto/driver.capnp
  )
  add_custom_command(
    OUTPUT ${CMAKE_CURRENT_BINARY_DIR}/hello.capnp.c ${CMAKE_CURRENT_BINARY_DIR}/hello.capnp.h
    COMMAND ${CMAKE_SOURCE_DIR}/scripts/mock_capnpc.sh ${CMAKE_SOURCE_DIR}/proto/hello.capnp
    DEPENDS ${CMAKE_SOURCE_DIR}/proto/hello.capnp
  )
  add_library(capnp STATIC
    libos/capnp/capnp_helpers.c
    ${CMAKE_CURRENT_BINARY_DIR}/driver.capnp.c
    ${CMAKE_CURRENT_BINARY_DIR}/hello.capnp.c
  )
  target_include_directories(capnp PUBLIC
    ${CMAKE_SOURCE_DIR}/proto
    ${CMAKE_SOURCE_DIR}/libos/capnp
  )
endif()

add_executable(kernel ${KERNEL_SOURCES})

if(USE_TICKET_LOCK)
  target_compile_definitions(kernel PRIVATE USE_TICKET_LOCK)
endif()
if(IPC_DEBUG)
  target_compile_definitions(kernel PRIVATE IPC_DEBUG)
endif()
if(USE_SIMD)
  target_compile_definitions(kernel PRIVATE USE_SIMD)
endif()

# QEMU executable used for run targets
find_program(QEMU_EXECUTABLE
  NAMES qemu-system-x86_64 qemu-system-i386 qemu
  DOC "QEMU system emulator")

set(CPUFLAGS "" CACHE STRING "Additional CPU specific compile flags")

target_include_directories(kernel PRIVATE
  ${CMAKE_SOURCE_DIR}
  ${CMAKE_SOURCE_DIR}/include
  ${CMAKE_SOURCE_DIR}/kernel/include
  ${CMAKE_SOURCE_DIR}/proto
  ${CMAKE_SOURCE_DIR}/libos/capnp
  ${CMAKE_SOURCE_DIR}/src
  ${CMAKE_SOURCE_DIR}/src/arch/x86/legacy
  ${CMAKE_SOURCE_DIR}/src/arch/x86/modern
  ${CMAKE_SOURCE_DIR}/libos/stubs
)

if(CPUFLAGS)
  target_compile_options(kernel PRIVATE ${CPUFLAGS})
endif()

target_link_libraries(kernel PRIVATE nstr_graph ddekit)
if(USE_CAPNP)
  target_link_libraries(kernel PRIVATE capnp)
endif()

add_subdirectory(src/ddekit)

add_subdirectory(src/libnstr_graph)

if(QEMU_EXECUTABLE)
  add_custom_target(qemu-nox
    COMMAND ${QEMU_EXECUTABLE} -nographic -serial stdio -kernel $<TARGET_FILE:kernel>
    DEPENDS kernel
    USES_TERMINAL
  )
endif()

add_executable(msgqueue_demo demos/msgqueue_demo.c)
target_include_directories(msgqueue_demo PRIVATE
  ${CMAKE_SOURCE_DIR}
  ${CMAKE_SOURCE_DIR}/include
  ${CMAKE_SOURCE_DIR}/proto
)
target_link_libraries(msgqueue_demo PRIVATE libos nstr_graph)
if(USE_CAPNP)
  target_link_libraries(msgqueue_demo PRIVATE capnp)
endif()

add_executable(fib_big_demo demos/fib_big_demo.c)
target_include_directories(fib_big_demo PRIVATE
  ${CMAKE_SOURCE_DIR}
  ${CMAKE_SOURCE_DIR}/include
  ${CMAKE_SOURCE_DIR}/proto
)
target_link_libraries(fib_big_demo PRIVATE libos nstr_graph)
if(USE_CAPNP)
  target_link_libraries(fib_big_demo PRIVATE capnp)
endif()

add_executable(wumpus demos/wumpus.c)
target_include_directories(wumpus PRIVATE
  ${CMAKE_SOURCE_DIR}/include
)
target_link_libraries(wumpus PRIVATE libos)

add_executable(phoenix_prof tools/phoenix_metrics.c)
target_include_directories(phoenix_prof PRIVATE
  ${CMAKE_SOURCE_DIR}
)
target_compile_definitions(phoenix_prof PRIVATE PHOENIX_METRICS_MAIN)

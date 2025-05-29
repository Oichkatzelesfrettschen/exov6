cmake_minimum_required(VERSION 3.16)

if(NOT DEFINED CMAKE_C_COMPILER)
  set(CMAKE_C_COMPILER clang)
endif()
if(NOT DEFINED CMAKE_CXX_COMPILER)
  set(CMAKE_CXX_COMPILER clang++)
endif()

project(xv6 LANGUAGES C CXX)

option(USE_TICKET_LOCK "Use ticket-based spinlocks" OFF)
option(IPC_DEBUG "Enable IPC debug logging" OFF)
option(USE_CAPNP "Build Cap'n Proto support" OFF)
option(USE_SIMD "Enable SIMD math routines" OFF)
option(MCU "Build for Cortex-M microcontroller" OFF)

include(CheckCCompilerFlag)
check_c_compiler_flag("-std=c23" HAVE_STD_C23)
if(HAVE_STD_C23)
  add_compile_options(-std=c23)
  set(CMAKE_C_STANDARD 23)
  set(CMAKE_C_STANDARD_REQUIRED ON)
else()
  check_c_compiler_flag("-std=c2x" HAVE_STD_C2X)
  if(HAVE_STD_C2X)
    add_compile_options(-std=c2x)
  endif()
endif()
set(CMAKE_CXX_STANDARD 23)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_EXPORT_COMPILE_COMMANDS ON)
add_compile_options(-Wall -Werror)

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
if(CLANG_TIDY_EXE)
  set(CMAKE_C_CLANG_TIDY "${CLANG_TIDY_EXE}")
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
  add_executable(kernel src/arch/mcu/startup.c kernel/picokernel.c user/blink.c)
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
file(GLOB_RECURSE PICO_SOURCES kernel/pico/*.c)
file(GLOB_RECURSE ARCH_GENERIC_SOURCES src/arch/generic/*.c)
file(GLOB_RECURSE ARCH_X86_LEGACY_SOURCES src/arch/x86/legacy/*.c)
file(GLOB_RECURSE ARCH_X86_MODERN_SOURCES src/arch/x86/modern/*.c)
list(APPEND KERNEL_SOURCES
  ${PICO_SOURCES}
  ${ARCH_GENERIC_SOURCES}
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

file(GLOB LIBPOSIX_SOURCES userspace/libposix/*.c)
file(GLOB LIBBAREMETAL_SOURCES userspace/libbaremetal/*.c)
file(GLOB LIB9P_SOURCES userspace/lib9p/*.c)

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
  libos/driver.c
  libos/affine_runtime.c
  libos/env.c
  libos/ipc.c
  libos/posix.c
  libos/termios.c
  libos/microkernel/cap.c
  libos/microkernel/msg_router.c
  libos/microkernel/resource_account.c
  libos/microkernel/registration.c
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
  ${CMAKE_SOURCE_DIR}/kernel/pico
  ${CMAKE_SOURCE_DIR}/src
  ${CMAKE_SOURCE_DIR}/src/arch/generic
  ${CMAKE_SOURCE_DIR}/src/arch/x86/legacy
  ${CMAKE_SOURCE_DIR}/src/arch/x86/modern
  ${CMAKE_SOURCE_DIR}/userspace/libposix
  ${CMAKE_SOURCE_DIR}/userspace/libbaremetal
  ${CMAKE_SOURCE_DIR}/userspace/lib9p
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
  ${CMAKE_SOURCE_DIR}/kernel/pico
  ${CMAKE_SOURCE_DIR}/src
  ${CMAKE_SOURCE_DIR}/src/arch/generic
  ${CMAKE_SOURCE_DIR}/src/arch/x86/legacy
  ${CMAKE_SOURCE_DIR}/src/arch/x86/modern
  ${CMAKE_SOURCE_DIR}/userspace/libposix
  ${CMAKE_SOURCE_DIR}/userspace/libbaremetal
  ${CMAKE_SOURCE_DIR}/userspace/lib9p
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

add_executable(msgqueue_demo examples/demos/msgqueue_demo.c)
target_include_directories(msgqueue_demo PRIVATE
  ${CMAKE_SOURCE_DIR}
  ${CMAKE_SOURCE_DIR}/include
  ${CMAKE_SOURCE_DIR}/proto
)
target_link_libraries(msgqueue_demo PRIVATE libos nstr_graph)
if(USE_CAPNP)
  target_link_libraries(msgqueue_demo PRIVATE capnp)
endif()

add_executable(fib_big_demo examples/demos/fib_big_demo.c)
target_include_directories(fib_big_demo PRIVATE
  ${CMAKE_SOURCE_DIR}
  ${CMAKE_SOURCE_DIR}/include
  ${CMAKE_SOURCE_DIR}/proto
)
target_link_libraries(fib_big_demo PRIVATE libos nstr_graph)
if(USE_CAPNP)
  target_link_libraries(fib_big_demo PRIVATE capnp)
endif()

add_executable(wumpus examples/demos/wumpus.c)
target_include_directories(wumpus PRIVATE
  ${CMAKE_SOURCE_DIR}/include
)
target_link_libraries(wumpus PRIVATE libos)

add_executable(phoenix_prof tools/profiling/phoenix_metrics.c)
target_include_directories(phoenix_prof PRIVATE
  ${CMAKE_SOURCE_DIR}
)
target_compile_definitions(phoenix_prof PRIVATE PHOENIX_METRICS_MAIN)

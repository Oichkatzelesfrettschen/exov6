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

set(CMAKE_C_STANDARD 23)
set(CMAKE_C_STANDARD_REQUIRED ON)
set(CMAKE_CXX_STANDARD 23)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_EXPORT_COMPILE_COMMANDS ON)
add_compile_options(-Wall -Werror)

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
    engine/proto/example.y
    ${CMAKE_CURRENT_BINARY_DIR}/example_parser.c
    DEFINES_FILE ${CMAKE_CURRENT_BINARY_DIR}/example_parser.h)
  add_custom_target(example_bison DEPENDS ${BISON_example_parser_OUTPUTS})
endif()

file(GLOB_RECURSE KERNEL_SOURCES
  engine/kernel/*.c
)
list(APPEND KERNEL_SOURCES engine/kernel/runqueue.c)

set(LIBOS_SOURCES
  engine/user/ulib.c
  engine/user/printf.c
  engine/user/umalloc.c
  engine/user/caplib.c
  engine/user/chan.c
  engine/user/door.c
  engine/user/math_core.c
  engine/user/libos/sched.c
  engine/libos/fs.c
  engine/libos/file.c
  engine/libos/driver.c
  engine/libos/affine_runtime.c
  engine/libos/env.c
  engine/libos/ipc.c
  engine/libos/posix.c
  engine/libos/termios.c
  engine/libos/microkernel/cap.c
  engine/libos/microkernel/msg_router.c
  engine/libos/microkernel/resource_account.c
  engine/libos/microkernel/registration.c
)
add_library(libos STATIC ${LIBOS_SOURCES})
target_include_directories(libos PUBLIC
  ${CMAKE_SOURCE_DIR}
  ${CMAKE_SOURCE_DIR}/engine/include
  ${CMAKE_SOURCE_DIR}/engine/proto
  ${CMAKE_SOURCE_DIR}/engine/libos/include
  ${CMAKE_SOURCE_DIR}/engine/libos/capnp
)

if(USE_CAPNP)
  add_custom_command(
    OUTPUT ${CMAKE_CURRENT_BINARY_DIR}/driver.capnp.c ${CMAKE_CURRENT_BINARY_DIR}/driver.capnp.h
    COMMAND ${CMAKE_SOURCE_DIR}/scripts/mock_capnpc.sh ${CMAKE_SOURCE_DIR}/engine/proto/driver.capnp
    DEPENDS ${CMAKE_SOURCE_DIR}/engine/proto/driver.capnp
  )
  add_custom_command(
    OUTPUT ${CMAKE_CURRENT_BINARY_DIR}/hello.capnp.c ${CMAKE_CURRENT_BINARY_DIR}/hello.capnp.h
    COMMAND ${CMAKE_SOURCE_DIR}/scripts/mock_capnpc.sh ${CMAKE_SOURCE_DIR}/engine/proto/hello.capnp
    DEPENDS ${CMAKE_SOURCE_DIR}/engine/proto/hello.capnp
  )
  add_library(capnp STATIC
    engine/libos/capnp/capnp_helpers.c
    ${CMAKE_CURRENT_BINARY_DIR}/driver.capnp.c
    ${CMAKE_CURRENT_BINARY_DIR}/hello.capnp.c
  )
  target_include_directories(capnp PUBLIC
    ${CMAKE_SOURCE_DIR}/engine/proto
    ${CMAKE_SOURCE_DIR}/engine/libos/capnp
  )
endif()

add_executable(kernel ${KERNEL_SOURCES})

if(USE_TICKET_LOCK)
  target_compile_definitions(kernel PRIVATE USE_TICKET_LOCK)
endif()
if(IPC_DEBUG)
  target_compile_definitions(kernel PRIVATE IPC_DEBUG)
endif()

# QEMU executable used for run targets
find_program(QEMU_EXECUTABLE
  NAMES qemu-system-x86_64 qemu-system-i386 qemu
  DOC "QEMU system emulator")

set(CPUFLAGS "" CACHE STRING "Additional CPU specific compile flags")

target_include_directories(kernel PRIVATE
  ${CMAKE_SOURCE_DIR}
  ${CMAKE_SOURCE_DIR}/engine/include
  ${CMAKE_SOURCE_DIR}/engine/kernel/include
  ${CMAKE_SOURCE_DIR}/engine/proto
  ${CMAKE_SOURCE_DIR}/engine/libos/include
  ${CMAKE_SOURCE_DIR}/engine/libos/capnp
)

if(CPUFLAGS)
  target_compile_options(kernel PRIVATE ${CPUFLAGS})
endif()

target_link_libraries(kernel PRIVATE nstr_graph)
if(USE_CAPNP)
  target_link_libraries(kernel PRIVATE capnp)
endif()

add_subdirectory(libnstr_graph)

if(QEMU_EXECUTABLE)
  add_custom_target(qemu-nox
    COMMAND ${QEMU_EXECUTABLE} -nographic -serial stdio -kernel $<TARGET_FILE:kernel>
    DEPENDS kernel
    USES_TERMINAL
  )
endif()

add_executable(msgqueue_demo engine/user/user/msgqueue_demo.c)
target_include_directories(msgqueue_demo PRIVATE
  ${CMAKE_SOURCE_DIR}
  ${CMAKE_SOURCE_DIR}/engine/include
  ${CMAKE_SOURCE_DIR}/engine/proto
  ${CMAKE_SOURCE_DIR}/engine/libos/include
)
target_link_libraries(msgqueue_demo PRIVATE libos nstr_graph)
if(USE_CAPNP)
  target_link_libraries(msgqueue_demo PRIVATE capnp)
endif()

add_executable(wumpus engine/user/user/wumpus.c)
target_include_directories(wumpus PRIVATE
  ${CMAKE_SOURCE_DIR}/engine/include
)
target_link_libraries(wumpus PRIVATE libos)

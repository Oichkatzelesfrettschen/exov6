# Phoenix Exokernel - Advanced Exokernel with Granular CMake Architecture
# CMake 3.25+ Best Practices - Modern Standards
cmake_minimum_required(VERSION 3.25...3.28 FATAL_ERROR)

# Policy settings for modern CMake
cmake_policy(VERSION 3.25)
if(POLICY CMP0135)
  cmake_policy(SET CMP0135 NEW) # FetchContent timestamp handling
endif()

# Set compilers before project declaration using toolchain or environment
if(NOT DEFINED CMAKE_C_COMPILER AND NOT CMAKE_TOOLCHAIN_FILE)
  set(CMAKE_C_COMPILER
      clang
      CACHE STRING "C compiler"
  )
endif()
if(NOT DEFINED CMAKE_CXX_COMPILER AND NOT CMAKE_TOOLCHAIN_FILE)
  set(CMAKE_CXX_COMPILER
      clang++
      CACHE STRING "C++ compiler"
  )
endif()

# Project declaration with full metadata
project(
  PhoenixExokernel
  VERSION 1.0.0
  DESCRIPTION "Phoenix Exokernel - Advanced Exokernel with Modern LLVM Toolchain"
  HOMEPAGE_URL "https://github.com/Oichkatzelesfrettschen/exov6"
  LANGUAGES C CXX ASM
)

# Configure CMake modules and settings
list(APPEND CMAKE_MODULE_PATH "${CMAKE_SOURCE_DIR}/cmake")
set(CMAKE_EXPORT_COMPILE_COMMANDS
    ON
    CACHE BOOL "Generate compile_commands.json"
)
set(CMAKE_COLOR_DIAGNOSTICS ON) # Enable colored output (CMake 3.24+)

# C/C++ Standards
set(CMAKE_C_STANDARD
    23
    CACHE STRING "C standard version"
)
set(CMAKE_C_STANDARD_REQUIRED ON)
set(CMAKE_C_EXTENSIONS OFF)
set(CMAKE_CXX_STANDARD
    23
    CACHE STRING "C++ standard version"
)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)

# Position Independent Code for all targets
set(CMAKE_POSITION_INDEPENDENT_CODE ON)

# Include our configuration modules
include(PhoenixConfig)
include(FindLLVMTools)
include(CompilerDetection)
include(FeatureDetection)

# ═══════════════════════════════════════════════════════════════════════════════
# BUILD OPTIONS - Modern CMake option() with categorization
# ═══════════════════════════════════════════════════════════════════════════════

# Core features
option(USE_LTO "Enable LLVM ThinLTO optimization" OFF)
option(USE_LLD "Use LLVM LLD linker" OFF)
option(USE_POLLY "Enable LLVM Polly optimizations" OFF)
option(USE_SIMD "Enable SIMD instruction support" OFF)
option(USE_CAPNP "Build Cap'n Proto support" OFF)

# Debug features
option(ENABLE_ASAN "Enable AddressSanitizer" OFF)
option(ENABLE_TSAN "Enable ThreadSanitizer" OFF)
option(ENABLE_UBSAN "Enable UndefinedBehaviorSanitizer" OFF)
option(ENABLE_MSAN "Enable MemorySanitizer" OFF)
option(IPC_DEBUG "Enable IPC debug logging" OFF)

# Platform features
option(MCU "Build for microcontroller target" OFF)
option(USE_TICKET_LOCK "Use ticket-based spinlocks" OFF)
option(ENABLE_AVX2 "Enable AVX2 instructions" OFF)
option(ENABLE_AVX512 "Enable AVX512 instructions" OFF)
option(ENABLE_NEON "Enable ARM NEON instructions" OFF)

# Security features
option(ENABLE_CET "Enable Intel CET" ON)
option(ENABLE_PAC "Enable ARM Pointer Authentication" ON)
option(ENABLE_STACK_PROTECTOR "Enable strong stack protection" ON)

# Build configuration
option(BUILD_DEMOS "Build demonstration programs" ON)
option(BUILD_TESTS "Build test suite" ON)
option(BUILD_TOOLS "Build development tools" ON)
option(BUILD_DOCS "Build documentation" OFF)

# ═══════════════════════════════════════════════════════════════════════════════
# COMPILER FLAGS - Applied globally with target_compile_options() pattern
# ═══════════════════════════════════════════════════════════════════════════════

# Security hardening flags
if(ENABLE_STACK_PROTECTOR)
  add_compile_options(-fstack-protector-strong)
endif()

if(ENABLE_CET AND CMAKE_SYSTEM_PROCESSOR MATCHES "x86_64")
  add_compile_options(-fcf-protection=full)
endif()

if(ENABLE_PAC AND CMAKE_SYSTEM_PROCESSOR MATCHES "aarch64")
  add_compile_options(-mbranch-protection=standard)
endif()

# ═══════════════════════════════════════════════════════════════════════════════
# GLOBAL CONFIGURATION
# ═══════════════════════════════════════════════════════════════════════════════

# Detect and configure LLVM toolchain
phoenix_detect_llvm_tools()

# Generate configuration header
generate_config_header()

# Modern include directory management (prefer target_include_directories)
include_directories("${CMAKE_BINARY_DIR}/include")

# ═══════════════════════════════════════════════════════════════════════════════
# ARCHITECTURAL ZONES - Modern subdirectory organization
# ═══════════════════════════════════════════════════════════════════════════════

# Zone 1: Architecture Layer (Base dependency)
add_subdirectory(src/arch)

# Zone 2: System Libraries (Depends on arch)
add_subdirectory(src/ddekit)
add_subdirectory(src/libnstr_graph)

# Zone 3: Protocols (Independent)
add_subdirectory(proto)

# Zone 4: Userland Core (Depends on protocols)
add_subdirectory(user)

# Zone 4.5: LibOS Reconstruction (Phase 3)
add_subdirectory(lib)

# Zone 5: Library OS (Depends on userland, protocols)
# add_subdirectory(libos)

# Zone 6: Kernel (Depends on arch, syslibs, protocols)
add_subdirectory(kernel)

# Zone 7: Tools (Independent, optional)
if(BUILD_TOOLS)
  add_subdirectory(tools)
endif()

# Zone 8: Demos (Depends on libos, userland, optional)
if(BUILD_DEMOS)
#  add_subdirectory(demos)
endif()

# Zone 9: Tests (Depends on all zones, optional)
if(BUILD_TESTS)
#  add_subdirectory(tests)
endif()

# Zone 10: Formal verification (Independent, optional)
if(EXISTS "${CMAKE_SOURCE_DIR}/formal/CMakeLists.txt")
  add_subdirectory(formal)
endif()

# Zone 11: Engine (Legacy mirror structure, optional)
if(EXISTS "${CMAKE_SOURCE_DIR}/engine/CMakeLists.txt")
  add_subdirectory(engine)
endif()

# ═══════════════════════════════════════════════════════════════════════════════
# RUNTIME TARGETS - Using generator expressions for modern CMake
# ═══════════════════════════════════════════════════════════════════════════════

# Find QEMU for runtime testing
find_program(
  QEMU_EXECUTABLE
  NAMES qemu-system-x86_64 qemu-system-i386 qemu
  DOC "QEMU system emulator"
)

if(QEMU_EXECUTABLE)
  # Basic QEMU target
  add_custom_target(
    qemu-nox
    COMMAND ${QEMU_EXECUTABLE} -nographic -serial stdio -kernel $<TARGET_FILE:kernel>
    DEPENDS kernel
    USES_TERMINAL
    COMMENT "Running Phoenix Exokernel in QEMU (no graphics)"
  )

  # Debug QEMU target
  add_custom_target(
    qemu-debug
    COMMAND ${QEMU_EXECUTABLE} -nographic -serial stdio -s -S -kernel $<TARGET_FILE:kernel>
    DEPENDS kernel
    USES_TERMINAL
    COMMENT "Running Phoenix Exokernel in QEMU with GDB server"
  )

  # KVM accelerated target (if available)
  if(HAVE_KVM)
    add_custom_target(
      qemu-kvm
      COMMAND ${QEMU_EXECUTABLE} -enable-kvm -nographic -serial stdio -kernel $<TARGET_FILE:kernel>
      DEPENDS kernel
      USES_TERMINAL
      COMMENT "Running Phoenix Exokernel in QEMU with KVM acceleration"
    )
  endif()
endif()

# ═══════════════════════════════════════════════════════════════════════════════
# INSTALLATION AND PACKAGING - Modern install() patterns
# ═══════════════════════════════════════════════════════════════════════════════

# Install kernel
install(TARGETS kernel RUNTIME DESTINATION bin COMPONENT kernel)

# Install development headers
install(
  DIRECTORY include/
  DESTINATION include/phoenix
  COMPONENT development
  FILES_MATCHING
  PATTERN "*.h"
)

# Install config header
install(
  FILES "${CMAKE_BINARY_DIR}/include/phoenix_config.h"
  DESTINATION include/phoenix
  COMPONENT development
)

# Package configuration - Modern CPack settings
set(CPACK_PACKAGE_NAME "PhoenixExokernel")
set(CPACK_PACKAGE_VERSION "${PROJECT_VERSION}")
set(CPACK_PACKAGE_DESCRIPTION "${PROJECT_DESCRIPTION}")
set(CPACK_PACKAGE_CONTACT "Phoenix Exokernel Development Team")
set(CPACK_GENERATOR "TGZ;DEB;RPM")
set(CPACK_SOURCE_GENERATOR "TGZ")
set(CPACK_PACKAGE_CHECKSUM "SHA256")

include(CPack)

# ═══════════════════════════════════════════════════════════════════════════════
# STATUS REPORT - Comprehensive configuration summary
# ═══════════════════════════════════════════════════════════════════════════════

message(STATUS "═══════════════════════════════════════════════════════════")
message(STATUS "Phoenix Exokernel Configuration Summary")
message(STATUS "═══════════════════════════════════════════════════════════")
message(STATUS "Version: ${PROJECT_VERSION}")
message(STATUS "Build type: ${CMAKE_BUILD_TYPE}")
message(STATUS "Compiler: ${CMAKE_C_COMPILER_ID} ${CMAKE_C_COMPILER_VERSION}")
message(STATUS "C Standard: ${CMAKE_C_STANDARD}")
message(STATUS "CXX Standard: ${CMAKE_CXX_STANDARD}")

if(EXOV6_LLVM_TOOLS_AVAILABLE)
  message(STATUS "LLVM toolchain: Available")
  if(USE_LLD)
    message(STATUS "  - LLD linker: Enabled")
  endif()
  if(USE_LTO)
    message(STATUS "  - ThinLTO: Enabled")
  endif()
  if(USE_POLLY)
    message(STATUS "  - Polly optimizations: Enabled")
  endif()
else()
  message(STATUS "LLVM toolchain: Not available")
endif()

message(STATUS "Architectural zones:")
message(STATUS "  - Architecture layer: ✓")
message(STATUS "  - System libraries: ✓")
message(STATUS "  - Protocols: ✓")
message(STATUS "  - Userland: ✓")
message(STATUS "  - Library OS: ✓")
message(STATUS "  - Kernel: ✓")
message(STATUS "  - Tools: ${BUILD_TOOLS}")
message(STATUS "  - Demos: ${BUILD_DEMOS}")
message(STATUS "  - Tests: ${BUILD_TESTS}")

if(ENABLE_ASAN
   OR ENABLE_TSAN
   OR ENABLE_UBSAN
   OR ENABLE_MSAN
)
  message(STATUS "Sanitizers enabled: ")
  if(ENABLE_ASAN)
    message(STATUS "  - AddressSanitizer")
  endif()
  if(ENABLE_TSAN)
    message(STATUS "  - ThreadSanitizer")
  endif()
  if(ENABLE_UBSAN)
    message(STATUS "  - UndefinedBehaviorSanitizer")
  endif()
  if(ENABLE_MSAN)
    message(STATUS "  - MemorySanitizer")
  endif()
endif()

message(STATUS "═══════════════════════════════════════════════════════════")

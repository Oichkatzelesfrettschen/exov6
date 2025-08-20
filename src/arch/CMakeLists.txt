# src/arch/CMakeLists.txt - Architecture-specific layer
# This is the base dependency layer for all architecture-specific code

# ═════════════════════════════════════════════════════════════════════
# SIMD DISPATCH LIBRARY
# ═════════════════════════════════════════════════════════════════════

set(SIMD_SOURCES simd_dispatch.c)

# Add architecture-specific SIMD implementations
if(CMAKE_SYSTEM_PROCESSOR MATCHES "x86_64|i.86")
    # x86/x64 SIMD sources
    list(APPEND SIMD_SOURCES
        x86/simd_x87.c
        x86/simd_mmx.c
        x86/simd_sse2.c
        x86/simd_avx.c
        x86/legacy/simd_mmx_cap.c
        x86/modern/simd_avx2_cap.c
    )
    
    # Set per-file compile options for SIMD instruction sets
    set_source_files_properties(x86/simd_mmx.c PROPERTIES COMPILE_OPTIONS "-mmmx")
    set_source_files_properties(x86/simd_sse2.c PROPERTIES COMPILE_OPTIONS "-msse2")
    set_source_files_properties(x86/simd_avx.c PROPERTIES COMPILE_OPTIONS "-mavx")
    set_source_files_properties(x86/legacy/simd_mmx_cap.c PROPERTIES COMPILE_OPTIONS "-mmmx")
    set_source_files_properties(x86/modern/simd_avx2_cap.c PROPERTIES COMPILE_OPTIONS "-mavx2")
    
    # Optional AVX512 if enabled
    if(ENABLE_AVX512 AND HAVE_AVX512F)
        list(APPEND SIMD_SOURCES x86/modern/simd_avx512_cap.c)
        set_source_files_properties(x86/modern/simd_avx512_cap.c PROPERTIES COMPILE_OPTIONS "-mavx512f")
    endif()
    
elseif(CMAKE_SYSTEM_PROCESSOR MATCHES "aarch64|arm")
    # ARM/AArch64 SIMD sources
    list(APPEND SIMD_SOURCES
        arm/simd_neon.c
        arm/simd_neon_cap.c
    )
    
    if(CMAKE_SYSTEM_PROCESSOR MATCHES "arm" AND NOT CMAKE_SYSTEM_PROCESSOR MATCHES "aarch64")
        # ARM32 needs explicit NEON flags
        set_source_files_properties(arm/simd_neon.c PROPERTIES COMPILE_OPTIONS "-mfpu=neon")
        set_source_files_properties(arm/simd_neon_cap.c PROPERTIES COMPILE_OPTIONS "-mfpu=neon")
    endif()
    
elseif(CMAKE_SYSTEM_PROCESSOR MATCHES "powerpc|ppc")
    # PowerPC AltiVec sources
    list(APPEND SIMD_SOURCES
        ppc/simd_altivec.c
        ppc/simd_altivec_cap.c
    )
    
    set_source_files_properties(ppc/simd_altivec.c PROPERTIES COMPILE_OPTIONS "-maltivec")
    set_source_files_properties(ppc/simd_altivec_cap.c PROPERTIES COMPILE_OPTIONS "-maltivec")
endif()

# Create SIMD dispatch library
exov6_add_library(exov6-simd
    STATIC
    SOURCES ${SIMD_SOURCES}
    INCLUDES 
        ${CMAKE_CURRENT_SOURCE_DIR}
        ${CMAKE_SOURCE_DIR}/tools
        ${CMAKE_SOURCE_DIR}/include
)

# Apply architecture-specific optimizations
configure_arch_optimizations(exov6-simd)

# ═════════════════════════════════════════════════════════════════════
# ARCHITECTURE-SPECIFIC LIBRARIES
# ═════════════════════════════════════════════════════════════════════

# x86 Legacy Support
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/x86/legacy")
    file(GLOB X86_LEGACY_SOURCES x86/legacy/*.c)
    if(X86_LEGACY_SOURCES)
        exov6_add_library(exov6-arch-x86-legacy
            STATIC
            SOURCES ${X86_LEGACY_SOURCES}
            INCLUDES 
                ${CMAKE_CURRENT_SOURCE_DIR}/x86/legacy
                ${CMAKE_SOURCE_DIR}/include
            DEPENDENCIES exov6-simd
        )
    endif()
endif()

# x86 Modern Support
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/x86/modern")
    file(GLOB X86_MODERN_SOURCES x86/modern/*.c)
    if(X86_MODERN_SOURCES)
        exov6_add_library(exov6-arch-x86-modern
            STATIC
            SOURCES ${X86_MODERN_SOURCES}
            INCLUDES 
                ${CMAKE_CURRENT_SOURCE_DIR}/x86/modern
                ${CMAKE_SOURCE_DIR}/include
            DEPENDENCIES exov6-simd
        )
    endif()
endif()

# ARM Support
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/arm")
    file(GLOB ARM_SOURCES arm/*.c)
    if(ARM_SOURCES)
        exov6_add_library(exov6-arch-arm
            STATIC
            SOURCES ${ARM_SOURCES}
            INCLUDES 
                ${CMAKE_CURRENT_SOURCE_DIR}/arm
                ${CMAKE_SOURCE_DIR}/include
            DEPENDENCIES exov6-simd
        )
    endif()
endif()

# AArch64 Support
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/aarch64")
    file(GLOB AARCH64_SOURCES aarch64/*.c)
    if(AARCH64_SOURCES)
        exov6_add_library(exov6-arch-aarch64
            STATIC
            SOURCES ${AARCH64_SOURCES}
            INCLUDES 
                ${CMAKE_CURRENT_SOURCE_DIR}/aarch64
                ${CMAKE_SOURCE_DIR}/include
            DEPENDENCIES exov6-simd
        )
    endif()
endif()

# PowerPC Support
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/ppc")
    file(GLOB PPC_SOURCES ppc/*.c)
    if(PPC_SOURCES)
        exov6_add_library(exov6-arch-ppc
            STATIC
            SOURCES ${PPC_SOURCES}
            INCLUDES 
                ${CMAKE_CURRENT_SOURCE_DIR}/ppc
                ${CMAKE_SOURCE_DIR}/include
            DEPENDENCIES exov6-simd
        )
    endif()
endif()

# MCU Support (if enabled)
if(MCU AND EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/mcu")
    file(GLOB MCU_SOURCES mcu/*.c)
    if(MCU_SOURCES)
        exov6_add_library(exov6-arch-mcu
            STATIC
            SOURCES ${MCU_SOURCES}
            INCLUDES 
                ${CMAKE_CURRENT_SOURCE_DIR}/mcu
                ${CMAKE_SOURCE_DIR}/include
        )
        
        # MCU-specific optimizations
        target_compile_definitions(exov6-arch-mcu PRIVATE MCU=1)
        target_compile_options(exov6-arch-mcu PRIVATE -Os)  # Optimize for size
    endif()
endif()

# Generic architecture sources
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/generic")
    file(GLOB GENERIC_SOURCES generic/*.c)
    if(GENERIC_SOURCES)
        exov6_add_library(exov6-arch-generic
            STATIC
            SOURCES ${GENERIC_SOURCES}
            INCLUDES 
                ${CMAKE_CURRENT_SOURCE_DIR}/generic
                ${CMAKE_SOURCE_DIR}/include
        )
    endif()
endif()

# ═════════════════════════════════════════════════════════════════════
# ARCHITECTURE META-LIBRARY
# ═════════════════════════════════════════════════════════════════════

# Create a meta-library that includes all relevant architecture components
set(ARCH_DEPENDENCIES exov6-simd)

# Add platform-specific libraries
if(CMAKE_SYSTEM_PROCESSOR MATCHES "x86_64|i.86")
    if(TARGET exov6-arch-x86-legacy)
        list(APPEND ARCH_DEPENDENCIES exov6-arch-x86-legacy)
    endif()
    if(TARGET exov6-arch-x86-modern)
        list(APPEND ARCH_DEPENDENCIES exov6-arch-x86-modern)
    endif()
elseif(CMAKE_SYSTEM_PROCESSOR MATCHES "aarch64")
    if(TARGET exov6-arch-aarch64)
        list(APPEND ARCH_DEPENDENCIES exov6-arch-aarch64)
    endif()
elseif(CMAKE_SYSTEM_PROCESSOR MATCHES "arm")
    if(TARGET exov6-arch-arm)
        list(APPEND ARCH_DEPENDENCIES exov6-arch-arm)
    endif()
elseif(CMAKE_SYSTEM_PROCESSOR MATCHES "powerpc|ppc")
    if(TARGET exov6-arch-ppc)
        list(APPEND ARCH_DEPENDENCIES exov6-arch-ppc)
    endif()
endif()

if(TARGET exov6-arch-generic)
    list(APPEND ARCH_DEPENDENCIES exov6-arch-generic)
endif()

if(MCU AND TARGET exov6-arch-mcu)
    list(APPEND ARCH_DEPENDENCIES exov6-arch-mcu)
endif()

# Create interface library that pulls in all architecture components
exov6_add_library(exov6-architecture
    INTERFACE
    DEPENDENCIES ${ARCH_DEPENDENCIES}
    INCLUDES 
        ${CMAKE_CURRENT_SOURCE_DIR}
        ${CMAKE_SOURCE_DIR}/include
)

# ═════════════════════════════════════════════════════════════════════
# EXPORTS
# ═════════════════════════════════════════════════════════════════════

# Export targets for use by other zones
set(EXOV6_ARCH_TARGETS
    exov6-simd
    exov6-architecture
    PARENT_SCOPE
)

message(STATUS "Architecture zone configured:")
message(STATUS "  - SIMD dispatch: ✓")
message(STATUS "  - Platform: ${CMAKE_SYSTEM_PROCESSOR}")
if(TARGET exov6-arch-x86-legacy)
    message(STATUS "  - x86 legacy: ✓")
endif()
if(TARGET exov6-arch-x86-modern)
    message(STATUS "  - x86 modern: ✓")
endif()
if(TARGET exov6-arch-arm)
    message(STATUS "  - ARM: ✓")
endif()
if(TARGET exov6-arch-aarch64)
    message(STATUS "  - AArch64: ✓")
endif()
if(TARGET exov6-arch-ppc)
    message(STATUS "  - PowerPC: ✓")
endif()
if(MCU AND TARGET exov6-arch-mcu)
    message(STATUS "  - MCU: ✓")
endif()
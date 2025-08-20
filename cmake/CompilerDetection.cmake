# CompilerDetection.cmake - Detect and configure compiler capabilities

include(CheckCCompilerFlag)
include(CheckCXXCompilerFlag)

# Detect compiler and set appropriate flags
function(detect_and_configure_compiler)
    # Check if we're using Clang
    if(CMAKE_C_COMPILER_ID MATCHES "Clang")
        set(EXOV6_USING_CLANG TRUE PARENT_SCOPE)
        message(STATUS "Detected Clang compiler: ${CMAKE_C_COMPILER_VERSION}")
        
        # Check for Clang-specific features
        check_c_compiler_flag("-flto=thin" SUPPORTS_THIN_LTO)
        check_c_compiler_flag("-fuse-ld=lld" SUPPORTS_LLD)
        check_c_compiler_flag("-mllvm -polly" SUPPORTS_POLLY)
        
        set(SUPPORTS_THIN_LTO ${SUPPORTS_THIN_LTO} PARENT_SCOPE)
        set(SUPPORTS_LLD ${SUPPORTS_LLD} PARENT_SCOPE)
        set(SUPPORTS_POLLY ${SUPPORTS_POLLY} PARENT_SCOPE)
        
    elseif(CMAKE_C_COMPILER_ID MATCHES "GNU")
        set(EXOV6_USING_GCC TRUE PARENT_SCOPE)
        message(STATUS "Detected GCC compiler: ${CMAKE_C_COMPILER_VERSION}")
        
        # Check for GCC-specific features
        check_c_compiler_flag("-flto" SUPPORTS_LTO)
        set(SUPPORTS_LTO ${SUPPORTS_LTO} PARENT_SCOPE)
        
    else()
        message(WARNING "Unsupported compiler: ${CMAKE_C_COMPILER_ID}")
        set(EXOV6_USING_UNKNOWN TRUE PARENT_SCOPE)
    endif()
    
    # Check for C23 support
    check_c_compiler_flag("-std=c2x" SUPPORTS_C23)
    if(NOT SUPPORTS_C23)
        message(FATAL_ERROR "Compiler does not support C23 standard (-std=c2x)")
    endif()
    
    # Check for common features
    check_c_compiler_flag("-march=native" SUPPORTS_MARCH_NATIVE)
    check_c_compiler_flag("-mtune=native" SUPPORTS_MTUNE_NATIVE)
    check_c_compiler_flag("-ffast-math" SUPPORTS_FAST_MATH)
    check_c_compiler_flag("-funroll-loops" SUPPORTS_UNROLL_LOOPS)
    
    set(SUPPORTS_MARCH_NATIVE ${SUPPORTS_MARCH_NATIVE} PARENT_SCOPE)
    set(SUPPORTS_MTUNE_NATIVE ${SUPPORTS_MTUNE_NATIVE} PARENT_SCOPE)
    set(SUPPORTS_FAST_MATH ${SUPPORTS_FAST_MATH} PARENT_SCOPE)
    set(SUPPORTS_UNROLL_LOOPS ${SUPPORTS_UNROLL_LOOPS} PARENT_SCOPE)
endfunction()

# Apply performance optimizations based on compiler capabilities
function(apply_performance_optimizations target)
    if(EXOV6_USING_CLANG)
        # Clang-specific optimizations
        target_compile_options(${target} PRIVATE
            $<$<CONFIG:Release>:-O3>
            $<$<CONFIG:Release>:-fomit-frame-pointer>
        )
        
        if(SUPPORTS_MARCH_NATIVE)
            target_compile_options(${target} PRIVATE
                $<$<CONFIG:Release>:-march=native>
            )
        endif()
        
        if(SUPPORTS_MTUNE_NATIVE)
            target_compile_options(${target} PRIVATE
                $<$<CONFIG:Release>:-mtune=native>
            )
        endif()
        
    elseif(EXOV6_USING_GCC)
        # GCC-specific optimizations
        target_compile_options(${target} PRIVATE
            $<$<CONFIG:Release>:-O3>
            $<$<CONFIG:Release>:-fomit-frame-pointer>
        )
        
        if(SUPPORTS_MARCH_NATIVE)
            target_compile_options(${target} PRIVATE
                $<$<CONFIG:Release>:-march=native>
            )
        endif()
        
        if(SUPPORTS_UNROLL_LOOPS)
            target_compile_options(${target} PRIVATE
                $<$<CONFIG:Release>:-funroll-loops>
            )
        endif()
    endif()
endfunction()

# Configure sanitizer support
function(configure_sanitizers target)
    if(EXOV6_USING_CLANG)
        # AddressSanitizer
        check_c_compiler_flag("-fsanitize=address" SUPPORTS_ASAN)
        if(SUPPORTS_ASAN AND ENABLE_ASAN)
            target_compile_options(${target} PRIVATE -fsanitize=address -fno-omit-frame-pointer)
            target_link_options(${target} PRIVATE -fsanitize=address)
        endif()
        
        # ThreadSanitizer
        check_c_compiler_flag("-fsanitize=thread" SUPPORTS_TSAN)
        if(SUPPORTS_TSAN AND ENABLE_TSAN)
            target_compile_options(${target} PRIVATE -fsanitize=thread)
            target_link_options(${target} PRIVATE -fsanitize=thread)
        endif()
        
        # UndefinedBehaviorSanitizer
        check_c_compiler_flag("-fsanitize=undefined" SUPPORTS_UBSAN)
        if(SUPPORTS_UBSAN AND ENABLE_UBSAN)
            target_compile_options(${target} PRIVATE -fsanitize=undefined)
            target_link_options(${target} PRIVATE -fsanitize=undefined)
        endif()
        
        # MemorySanitizer
        check_c_compiler_flag("-fsanitize=memory" SUPPORTS_MSAN)
        if(SUPPORTS_MSAN AND ENABLE_MSAN)
            target_compile_options(${target} PRIVATE -fsanitize=memory)
            target_link_options(${target} PRIVATE -fsanitize=memory)
        endif()
    endif()
endfunction()

# Configure architecture-specific optimizations
function(configure_arch_optimizations target)
    if(CMAKE_SYSTEM_PROCESSOR MATCHES "x86_64|AMD64")
        # x86_64 specific optimizations
        check_c_compiler_flag("-mavx2" SUPPORTS_AVX2)
        check_c_compiler_flag("-mavx512f" SUPPORTS_AVX512)
        
        if(SUPPORTS_AVX2 AND ENABLE_AVX2)
            target_compile_options(${target} PRIVATE -mavx2)
            target_compile_definitions(${target} PRIVATE HAVE_AVX2=1)
        endif()
        
        if(SUPPORTS_AVX512 AND ENABLE_AVX512)
            target_compile_options(${target} PRIVATE -mavx512f)
            target_compile_definitions(${target} PRIVATE HAVE_AVX512=1)
        endif()
        
    elseif(CMAKE_SYSTEM_PROCESSOR MATCHES "aarch64|arm64")
        # ARM64 specific optimizations
        check_c_compiler_flag("-mcpu=native" SUPPORTS_MCPU_NATIVE)
        if(SUPPORTS_MCPU_NATIVE)
            target_compile_options(${target} PRIVATE -mcpu=native)
        endif()
        
    elseif(CMAKE_SYSTEM_PROCESSOR MATCHES "arm")
        # ARM32 specific optimizations
        check_c_compiler_flag("-mfpu=neon" SUPPORTS_NEON)
        if(SUPPORTS_NEON AND ENABLE_NEON)
            target_compile_options(${target} PRIVATE -mfpu=neon)
            target_compile_definitions(${target} PRIVATE HAVE_NEON=1)
        endif()
    endif()
endfunction()

# Main compiler detection and configuration
detect_and_configure_compiler()

# Report capabilities
message(STATUS "Compiler capabilities:")
if(SUPPORTS_THIN_LTO)
    message(STATUS "  - ThinLTO: Available")
else()
    message(STATUS "  - ThinLTO: Not available")
endif()

if(SUPPORTS_LLD)
    message(STATUS "  - LLD linker: Available")
else()
    message(STATUS "  - LLD linker: Not available")
endif()

if(SUPPORTS_POLLY)
    message(STATUS "  - Polly optimizations: Available")
else()
    message(STATUS "  - Polly optimizations: Not available")
endif()
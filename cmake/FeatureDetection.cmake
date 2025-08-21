# FeatureDetection.cmake - Detect system and library features

include(CheckIncludeFile)
include(CheckFunctionExists)
include(CheckSymbolExists)
include(CheckLibraryExists)
include(CheckTypeSize)

# Detect system headers and functions
function(detect_system_features)
    # Check for standard headers
    check_include_file("stdatomic.h" HAVE_STDATOMIC_H)
    check_include_file("stdnoreturn.h" HAVE_STDNORETURN_H)
    check_include_file("threads.h" HAVE_THREADS_H)
    check_include_file("stdalign.h" HAVE_STDALIGN_H)
    check_include_file("sys/mman.h" HAVE_SYS_MMAN_H)
    check_include_file("sys/prctl.h" HAVE_SYS_PRCTL_H)
    check_include_file("linux/seccomp.h" HAVE_LINUX_SECCOMP_H)
    
    # Check for C23 features
    check_symbol_exists("_Static_assert" "assert.h" HAVE_STATIC_ASSERT)
    check_symbol_exists("_Generic" "stddef.h" HAVE_GENERIC)
    
    # Check for functions
    check_function_exists("mmap" HAVE_MMAP)
    check_function_exists("mprotect" HAVE_MPROTECT)
    check_function_exists("prctl" HAVE_PRCTL)
    check_function_exists("seccomp" HAVE_SECCOMP)
    check_function_exists("clone" HAVE_CLONE)
    check_function_exists("epoll_create1" HAVE_EPOLL)
    check_function_exists("eventfd" HAVE_EVENTFD)
    check_function_exists("signalfd" HAVE_SIGNALFD)
    check_function_exists("timerfd_create" HAVE_TIMERFD)
    
    # Check for library functions
    check_library_exists("rt" "clock_gettime" "" HAVE_LIBRT)
    check_library_exists("pthread" "pthread_create" "" HAVE_LIBPTHREAD)
    check_library_exists("numa" "numa_available" "" HAVE_LIBNUMA)
    
    # Check type sizes
    check_type_size("void*" SIZEOF_VOID_P)
    check_type_size("long" SIZEOF_LONG)
    check_type_size("size_t" SIZEOF_SIZE_T)
    
    # Set variables in parent scope
    set(HAVE_STDATOMIC_H ${HAVE_STDATOMIC_H} PARENT_SCOPE)
    set(HAVE_STDNORETURN_H ${HAVE_STDNORETURN_H} PARENT_SCOPE)
    set(HAVE_THREADS_H ${HAVE_THREADS_H} PARENT_SCOPE)
    set(HAVE_STDALIGN_H ${HAVE_STDALIGN_H} PARENT_SCOPE)
    set(HAVE_SYS_MMAN_H ${HAVE_SYS_MMAN_H} PARENT_SCOPE)
    set(HAVE_SYS_PRCTL_H ${HAVE_SYS_PRCTL_H} PARENT_SCOPE)
    set(HAVE_LINUX_SECCOMP_H ${HAVE_LINUX_SECCOMP_H} PARENT_SCOPE)
    set(HAVE_STATIC_ASSERT ${HAVE_STATIC_ASSERT} PARENT_SCOPE)
    set(HAVE_GENERIC ${HAVE_GENERIC} PARENT_SCOPE)
    set(HAVE_MMAP ${HAVE_MMAP} PARENT_SCOPE)
    set(HAVE_MPROTECT ${HAVE_MPROTECT} PARENT_SCOPE)
    set(HAVE_PRCTL ${HAVE_PRCTL} PARENT_SCOPE)
    set(HAVE_SECCOMP ${HAVE_SECCOMP} PARENT_SCOPE)
    set(HAVE_CLONE ${HAVE_CLONE} PARENT_SCOPE)
    set(HAVE_EPOLL ${HAVE_EPOLL} PARENT_SCOPE)
    set(HAVE_EVENTFD ${HAVE_EVENTFD} PARENT_SCOPE)
    set(HAVE_SIGNALFD ${HAVE_SIGNALFD} PARENT_SCOPE)
    set(HAVE_TIMERFD ${HAVE_TIMERFD} PARENT_SCOPE)
    set(HAVE_LIBRT ${HAVE_LIBRT} PARENT_SCOPE)
    set(HAVE_LIBPTHREAD ${HAVE_LIBPTHREAD} PARENT_SCOPE)
    set(HAVE_LIBNUMA ${HAVE_LIBNUMA} PARENT_SCOPE)
    set(SIZEOF_VOID_P ${SIZEOF_VOID_P} PARENT_SCOPE)
    set(SIZEOF_LONG ${SIZEOF_LONG} PARENT_SCOPE)
    set(SIZEOF_SIZE_T ${SIZEOF_SIZE_T} PARENT_SCOPE)
endfunction()

# Detect SIMD capabilities
function(detect_simd_features)
    include(CheckCSourceCompiles)
    
    # Check for x86 SIMD
    if(CMAKE_SYSTEM_PROCESSOR MATCHES "x86_64|i386")
        check_c_source_compiles("
            #include <immintrin.h>
            int main() {
                __m128i a = _mm_setzero_si128();
                return 0;
            }
        " HAVE_SSE2)
        
        check_c_source_compiles("
            #include <immintrin.h>
            int main() {
                __m256i a = _mm256_setzero_si256();
                return 0;
            }
        " HAVE_AVX2)
        
        check_c_source_compiles("
            #include <immintrin.h>
            int main() {
                __m512i a = _mm512_setzero_si512();
                return 0;
            }
        " HAVE_AVX512F)
        
        set(HAVE_SSE2 ${HAVE_SSE2} PARENT_SCOPE)
        set(HAVE_AVX2 ${HAVE_AVX2} PARENT_SCOPE)
        set(HAVE_AVX512F ${HAVE_AVX512F} PARENT_SCOPE)
    endif()
    
    # Check for ARM NEON
    if(CMAKE_SYSTEM_PROCESSOR MATCHES "arm|aarch64")
        check_c_source_compiles("
            #include <arm_neon.h>
            int main() {
                uint32x4_t a = vdupq_n_u32(0);
                return 0;
            }
        " HAVE_NEON)
        
        set(HAVE_NEON ${HAVE_NEON} PARENT_SCOPE)
    endif()
    
    # Check for PowerPC Altivec
    if(CMAKE_SYSTEM_PROCESSOR MATCHES "powerpc|ppc")
        check_c_source_compiles("
            #include <altivec.h>
            int main() {
                vector unsigned int a = vec_splat_u32(0);
                return 0;
            }
        " HAVE_ALTIVEC)
        
        set(HAVE_ALTIVEC ${HAVE_ALTIVEC} PARENT_SCOPE)
    endif()
endfunction()

# Detect virtualization features
function(detect_virtualization_features)
    # Check for KVM
    if(EXISTS "/dev/kvm")
        set(HAVE_KVM TRUE PARENT_SCOPE)
    else()
        set(HAVE_KVM FALSE PARENT_SCOPE)
    endif()
    
    # Check for hypervisor presence
    if(EXISTS "/sys/hypervisor/type")
        file(READ "/sys/hypervisor/type" HYPERVISOR_TYPE)
        string(STRIP "${HYPERVISOR_TYPE}" HYPERVISOR_TYPE)
        set(HYPERVISOR_TYPE ${HYPERVISOR_TYPE} PARENT_SCOPE)
        set(HAVE_HYPERVISOR TRUE PARENT_SCOPE)
    else()
        set(HAVE_HYPERVISOR FALSE PARENT_SCOPE)
    endif()
    
    # Check for container environment
    if(EXISTS "/proc/1/cgroup")
        file(READ "/proc/1/cgroup" CGROUP_CONTENT)
        if(CGROUP_CONTENT MATCHES "docker|lxc|systemd")
            set(IN_CONTAINER TRUE PARENT_SCOPE)
        else()
            set(IN_CONTAINER FALSE PARENT_SCOPE)
        endif()
    else()
        set(IN_CONTAINER FALSE PARENT_SCOPE)
    endif()
endfunction()

# Detect hardware features
function(detect_hardware_features)
    # Detect CPU count
    include(ProcessorCount)
    ProcessorCount(CPU_COUNT)
    set(CPU_COUNT ${CPU_COUNT} PARENT_SCOPE)
    
    # Detect memory size (Linux-specific)
    if(EXISTS "/proc/meminfo")
        file(READ "/proc/meminfo" MEMINFO)
        string(REGEX MATCH "MemTotal:[ ]*([0-9]+)" _ ${MEMINFO})
        if(CMAKE_MATCH_1)
            math(EXPR MEMORY_SIZE_MB "${CMAKE_MATCH_1} / 1024")
            set(MEMORY_SIZE_MB ${MEMORY_SIZE_MB} PARENT_SCOPE)
        endif()
    endif()
    
    # Detect page size
    if(CMAKE_SYSTEM_NAME STREQUAL "Linux")
        execute_process(
            COMMAND getconf PAGESIZE
            OUTPUT_VARIABLE PAGE_SIZE
            OUTPUT_STRIP_TRAILING_WHITESPACE
            ERROR_QUIET
        )
        if(PAGE_SIZE)
            set(PAGE_SIZE ${PAGE_SIZE} PARENT_SCOPE)
        else()
            set(PAGE_SIZE 4096 PARENT_SCOPE)  # Default assumption
        endif()
    endif()
endfunction()

# Apply feature-based configuration to target
function(apply_feature_config target)
    if(HAVE_STDATOMIC_H)
        target_compile_definitions(${target} PRIVATE HAVE_STDATOMIC_H=1)
    endif()
    
    if(HAVE_THREADS_H)
        target_compile_definitions(${target} PRIVATE HAVE_THREADS_H=1)
    endif()
    
    if(HAVE_MMAP)
        target_compile_definitions(${target} PRIVATE HAVE_MMAP=1)
    endif()
    
    if(HAVE_EPOLL)
        target_compile_definitions(${target} PRIVATE HAVE_EPOLL=1)
    endif()
    
    if(HAVE_KVM)
        target_compile_definitions(${target} PRIVATE HAVE_KVM=1)
    endif()
    
    if(CPU_COUNT)
        target_compile_definitions(${target} PRIVATE CPU_COUNT=${CPU_COUNT})
    endif()
    
    if(PAGE_SIZE)
        target_compile_definitions(${target} PRIVATE PAGE_SIZE=${PAGE_SIZE})
    endif()
    
    # SIMD features
    if(HAVE_SSE2)
        target_compile_definitions(${target} PRIVATE HAVE_SSE2=1)
    endif()
    
    if(HAVE_AVX2)
        target_compile_definitions(${target} PRIVATE HAVE_AVX2=1)
    endif()
    
    if(HAVE_NEON)
        target_compile_definitions(${target} PRIVATE HAVE_NEON=1)
    endif()
    
    if(HAVE_ALTIVEC)
        target_compile_definitions(${target} PRIVATE HAVE_ALTIVEC=1)
    endif()
endfunction()

# Generate config header
function(generate_config_header)
    configure_file(
        "${CMAKE_SOURCE_DIR}/cmake/config.h.in"
        "${CMAKE_BINARY_DIR}/include/exov6_config.h"
        @ONLY
    )
endfunction()

# Main feature detection
detect_system_features()
detect_simd_features()
detect_virtualization_features()
detect_hardware_features()

# Report detected features
message(STATUS "System features detected:")
message(STATUS "  - CPU cores: ${CPU_COUNT}")
if(MEMORY_SIZE_MB)
    message(STATUS "  - Memory: ${MEMORY_SIZE_MB} MB")
endif()
if(PAGE_SIZE)
    message(STATUS "  - Page size: ${PAGE_SIZE} bytes")
endif()
if(HAVE_KVM)
    message(STATUS "  - KVM: Available")
endif()
if(HAVE_HYPERVISOR)
    message(STATUS "  - Hypervisor: ${HYPERVISOR_TYPE}")
endif()
if(IN_CONTAINER)
    message(STATUS "  - Container: Detected")
endif()

# SIMD capabilities
if(HAVE_SSE2)
    message(STATUS "  - SSE2: Available")
endif()
if(HAVE_AVX2)
    message(STATUS "  - AVX2: Available")
endif()
if(HAVE_AVX512F)
    message(STATUS "  - AVX512F: Available")
endif()
if(HAVE_NEON)
    message(STATUS "  - NEON: Available")
endif()
if(HAVE_ALTIVEC)
    message(STATUS "  - AltiVec: Available")
endif()
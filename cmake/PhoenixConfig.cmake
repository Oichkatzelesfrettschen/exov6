# PhoenixConfig.cmake - Main configuration module for Phoenix Exokernel project

# Set project information
set(PHOENIX_VERSION_MAJOR 1)
set(PHOENIX_VERSION_MINOR 0)
set(PHOENIX_VERSION_PATCH 0)
set(PHOENIX_VERSION "${PHOENIX_VERSION_MAJOR}.${PHOENIX_VERSION_MINOR}.${PHOENIX_VERSION_PATCH}")

# Include required modules
include(CheckCCompilerFlag)
include(CheckCXXCompilerFlag)
include(CMakePackageConfigHelpers)

# Set C23 standard requirements
function(phoenix_set_standards target)
    set_target_properties(${target} PROPERTIES
        C_STANDARD 23
        C_STANDARD_REQUIRED ON
        C_EXTENSIONS OFF
        CXX_STANDARD 23
        CXX_STANDARD_REQUIRED ON
        CXX_EXTENSIONS OFF
    )
    target_compile_options(${target} PRIVATE -std=c2x)
endfunction()

# Apply common compile options
function(phoenix_apply_common_options target)
    target_compile_options(${target} PRIVATE
        -Wall
        # -Werror  # Temporarily disabled for CI/CD triage
        $<$<CONFIG:Debug>:-g3 -O0>
        $<$<CONFIG:Release>:-O3 -DNDEBUG>
        $<$<CONFIG:RelWithDebInfo>:-O2 -g>
        $<$<CONFIG:MinSizeRel>:-Os -DNDEBUG>
    )
    
    # Apply standards
    phoenix_set_standards(${target})
endfunction()

# Configure LLVM tools detection
function(phoenix_detect_llvm_tools)
    if(CMAKE_C_COMPILER_ID MATCHES "Clang")
        # Find LLVM tools with version suffix
        find_program(PHOENIX_LLVM_AR NAMES llvm-ar-18 llvm-ar)
        find_program(PHOENIX_LLVM_OBJCOPY NAMES llvm-objcopy-18 llvm-objcopy)
        find_program(PHOENIX_LLVM_STRIP NAMES llvm-strip-18 llvm-strip)
        find_program(PHOENIX_LLVM_NM NAMES llvm-nm-18 llvm-nm)
        find_program(PHOENIX_LLVM_OBJDUMP NAMES llvm-objdump-18 llvm-objdump)
        find_program(PHOENIX_LLVM_OPT NAMES opt-18 opt)
        
        if(PHOENIX_LLVM_AR)
            set(CMAKE_AR "${PHOENIX_LLVM_AR}" PARENT_SCOPE)
            message(STATUS "ExoV6: Using LLVM archiver: ${PHOENIX_LLVM_AR}")
        endif()
        
        if(PHOENIX_LLVM_OBJCOPY)
            set(CMAKE_OBJCOPY "${PHOENIX_LLVM_OBJCOPY}" PARENT_SCOPE)
        endif()
        
        if(PHOENIX_LLVM_STRIP)
            set(CMAKE_STRIP "${PHOENIX_LLVM_STRIP}" PARENT_SCOPE)
        endif()
        
        set(PHOENIX_LLVM_TOOLS_AVAILABLE TRUE PARENT_SCOPE)
    else()
        set(PHOENIX_LLVM_TOOLS_AVAILABLE FALSE PARENT_SCOPE)
        message(WARNING "ExoV6: LLVM tools require Clang compiler")
    endif()
endfunction()

# Configure modern LLVM features
function(phoenix_configure_llvm_features target)
    if(NOT CMAKE_C_COMPILER_ID MATCHES "Clang")
        message(WARNING "ExoV6: LLVM features require Clang compiler")
        return()
    endif()
    
    # LLD Linker
    if(USE_LLD)
        target_link_options(${target} PRIVATE -fuse-ld=lld)
        message(STATUS "ExoV6: Enabled LLD linker for ${target}")
    endif()
    
    # ThinLTO
    if(USE_LTO)
        set_target_properties(${target} PROPERTIES INTERPROCEDURAL_OPTIMIZATION ON)
        target_compile_options(${target} PRIVATE -flto=thin)
        target_link_options(${target} PRIVATE -flto=thin)
        message(STATUS "ExoV6: Enabled ThinLTO for ${target}")
    endif()
    
    # Polly optimizations
    if(USE_POLLY AND PHOENIX_LLVM_OPT)
        target_compile_options(${target} PRIVATE
            -mllvm -polly
        )
        message(STATUS "ExoV6: Enabled Polly optimizations for ${target}")
    endif()
    
    # Sanitizers
    if(ENABLE_ASAN)
        target_compile_options(${target} PRIVATE -fsanitize=address -fno-omit-frame-pointer)
        target_link_options(${target} PRIVATE -fsanitize=address)
        message(STATUS "ExoV6: Enabled AddressSanitizer for ${target}")
    endif()
    
    if(ENABLE_TSAN)
        target_compile_options(${target} PRIVATE -fsanitize=thread)
        target_link_options(${target} PRIVATE -fsanitize=thread)
        message(STATUS "ExoV6: Enabled ThreadSanitizer for ${target}")
    endif()
    
    if(ENABLE_UBSAN)
        target_compile_options(${target} PRIVATE -fsanitize=undefined)
        target_link_options(${target} PRIVATE -fsanitize=undefined)
        message(STATUS "ExoV6: Enabled UndefinedBehaviorSanitizer for ${target}")
    endif()
endfunction()

# Configure feature-based compilation
function(phoenix_configure_features target)
    if(USE_TICKET_LOCK)
        target_compile_definitions(${target} PRIVATE USE_TICKET_LOCK)
    endif()
    
    if(IPC_DEBUG)
        target_compile_definitions(${target} PRIVATE IPC_DEBUG)
    endif()
    
    if(USE_SIMD)
        target_compile_definitions(${target} PRIVATE USE_SIMD)
    endif()
    
    if(MCU)
        target_compile_definitions(${target} PRIVATE MCU=1)
    endif()
    
    # Decimal float support
    check_c_compiler_flag("-mdecimal-float" HAVE_DECIMAL_FLOAT)
    if(HAVE_DECIMAL_FLOAT)
        target_compile_options(${target} PRIVATE -mdecimal-float)
        target_compile_definitions(${target} PRIVATE HAVE_DECIMAL_FLOAT=1)
    endif()
endfunction()

# Create an ExoV6 library target with all configurations
function(phoenix_add_library target_name)
    cmake_parse_arguments(PHOENIX_LIB "STATIC;SHARED;INTERFACE" "TYPE" "SOURCES;INCLUDES;DEPENDENCIES;DEFINITIONS" ${ARGN})
    
    if(PHOENIX_LIB_STATIC OR (NOT PHOENIX_LIB_SHARED AND NOT PHOENIX_LIB_INTERFACE))
        set(lib_type STATIC)
    elseif(PHOENIX_LIB_SHARED)
        set(lib_type SHARED)
    elseif(PHOENIX_LIB_INTERFACE)
        set(lib_type INTERFACE)
    endif()
    
    if(lib_type STREQUAL "INTERFACE")
        add_library(${target_name} INTERFACE)
    else()
        add_library(${target_name} ${lib_type} ${PHOENIX_LIB_SOURCES})
    endif()
    
    # Apply common configurations
    if(NOT lib_type STREQUAL "INTERFACE")
        phoenix_apply_common_options(${target_name})
        phoenix_configure_llvm_features(${target_name})
        phoenix_configure_features(${target_name})
    endif()
    
    # Set include directories
    if(PHOENIX_LIB_INCLUDES)
        if(lib_type STREQUAL "INTERFACE")
            target_include_directories(${target_name} INTERFACE ${PHOENIX_LIB_INCLUDES})
        else()
            target_include_directories(${target_name} PUBLIC ${PHOENIX_LIB_INCLUDES})
        endif()
    endif()
    
    # Set dependencies
    if(PHOENIX_LIB_DEPENDENCIES)
        if(lib_type STREQUAL "INTERFACE")
            target_link_libraries(${target_name} INTERFACE ${PHOENIX_LIB_DEPENDENCIES})
        else()
            target_link_libraries(${target_name} PUBLIC ${PHOENIX_LIB_DEPENDENCIES})
        endif()
    endif()
    
    # Set definitions
    if(PHOENIX_LIB_DEFINITIONS)
        if(lib_type STREQUAL "INTERFACE")
            target_compile_definitions(${target_name} INTERFACE ${PHOENIX_LIB_DEFINITIONS})
        else()
            target_compile_definitions(${target_name} PUBLIC ${PHOENIX_LIB_DEFINITIONS})
        endif()
    endif()
    
    # Set properties for non-interface libraries
    if(NOT lib_type STREQUAL "INTERFACE")
        set_target_properties(${target_name} PROPERTIES
            POSITION_INDEPENDENT_CODE OFF
        )
    endif()
endfunction()

# Create an ExoV6 executable target with all configurations
function(phoenix_add_executable target_name)
    cmake_parse_arguments(PHOENIX_EXE "" "" "SOURCES;INCLUDES;DEPENDENCIES;DEFINITIONS" ${ARGN})
    
    add_executable(${target_name} ${PHOENIX_EXE_SOURCES})
    
    # Apply common configurations
    phoenix_apply_common_options(${target_name})
    phoenix_configure_llvm_features(${target_name})
    phoenix_configure_features(${target_name})
    
    # Set include directories
    if(PHOENIX_EXE_INCLUDES)
        target_include_directories(${target_name} PRIVATE ${PHOENIX_EXE_INCLUDES})
    endif()
    
    # Set dependencies
    if(PHOENIX_EXE_DEPENDENCIES)
        target_link_libraries(${target_name} PRIVATE ${PHOENIX_EXE_DEPENDENCIES})
    endif()
    
    # Set definitions
    if(PHOENIX_EXE_DEFINITIONS)
        target_compile_definitions(${target_name} PRIVATE ${PHOENIX_EXE_DEFINITIONS})
    endif()
    
    # Set properties
    set_target_properties(${target_name} PROPERTIES
        OUTPUT_NAME ${target_name}
    )
endfunction()

# Export configuration
set(EXOV6_CMAKE_DIR "${CMAKE_CURRENT_LIST_DIR}")
set(EXOV6_INCLUDE_DIRS 
    "${CMAKE_SOURCE_DIR}/include"
    "${CMAKE_SOURCE_DIR}/kernel/include"
    "${CMAKE_SOURCE_DIR}/proto"
)
# ExoV6Config.cmake - Main configuration module for ExoV6 project

# Set project information
set(EXOV6_VERSION_MAJOR 0)
set(EXOV6_VERSION_MINOR 6)
set(EXOV6_VERSION_PATCH 0)
set(EXOV6_VERSION "${EXOV6_VERSION_MAJOR}.${EXOV6_VERSION_MINOR}.${EXOV6_VERSION_PATCH}")

# Include required modules
include(CheckCCompilerFlag)
include(CheckCXXCompilerFlag)
include(CMakePackageConfigHelpers)

# Set C23 standard requirements
function(exov6_set_standards target)
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
function(exov6_apply_common_options target)
    target_compile_options(${target} PRIVATE
        -Wall
        -Werror
        $<$<CONFIG:Debug>:-g3 -O0>
        $<$<CONFIG:Release>:-O3 -DNDEBUG>
        $<$<CONFIG:RelWithDebInfo>:-O2 -g>
        $<$<CONFIG:MinSizeRel>:-Os -DNDEBUG>
    )
    
    # Apply standards
    exov6_set_standards(${target})
endfunction()

# Configure LLVM tools detection
function(exov6_detect_llvm_tools)
    if(CMAKE_C_COMPILER_ID MATCHES "Clang")
        # Find LLVM tools with version suffix
        find_program(EXOV6_LLVM_AR NAMES llvm-ar-18 llvm-ar)
        find_program(EXOV6_LLVM_OBJCOPY NAMES llvm-objcopy-18 llvm-objcopy)
        find_program(EXOV6_LLVM_STRIP NAMES llvm-strip-18 llvm-strip)
        find_program(EXOV6_LLVM_NM NAMES llvm-nm-18 llvm-nm)
        find_program(EXOV6_LLVM_OBJDUMP NAMES llvm-objdump-18 llvm-objdump)
        find_program(EXOV6_LLVM_OPT NAMES opt-18 opt)
        
        if(EXOV6_LLVM_AR)
            set(CMAKE_AR "${EXOV6_LLVM_AR}" PARENT_SCOPE)
            message(STATUS "ExoV6: Using LLVM archiver: ${EXOV6_LLVM_AR}")
        endif()
        
        if(EXOV6_LLVM_OBJCOPY)
            set(CMAKE_OBJCOPY "${EXOV6_LLVM_OBJCOPY}" PARENT_SCOPE)
        endif()
        
        if(EXOV6_LLVM_STRIP)
            set(CMAKE_STRIP "${EXOV6_LLVM_STRIP}" PARENT_SCOPE)
        endif()
        
        set(EXOV6_LLVM_TOOLS_AVAILABLE TRUE PARENT_SCOPE)
    else()
        set(EXOV6_LLVM_TOOLS_AVAILABLE FALSE PARENT_SCOPE)
        message(WARNING "ExoV6: LLVM tools require Clang compiler")
    endif()
endfunction()

# Configure modern LLVM features
function(exov6_configure_llvm_features target)
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
    if(USE_POLLY AND EXOV6_LLVM_OPT)
        target_compile_options(${target} PRIVATE
            -mllvm -polly
            -mllvm -polly-vectorizer=stripmine
            -mllvm -polly-parallel
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
function(exov6_configure_features target)
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
function(exov6_add_library target_name)
    cmake_parse_arguments(EXOV6_LIB "STATIC;SHARED;INTERFACE" "TYPE" "SOURCES;INCLUDES;DEPENDENCIES;DEFINITIONS" ${ARGN})
    
    if(EXOV6_LIB_STATIC OR (NOT EXOV6_LIB_SHARED AND NOT EXOV6_LIB_INTERFACE))
        set(lib_type STATIC)
    elseif(EXOV6_LIB_SHARED)
        set(lib_type SHARED)
    elseif(EXOV6_LIB_INTERFACE)
        set(lib_type INTERFACE)
    endif()
    
    if(lib_type STREQUAL "INTERFACE")
        add_library(${target_name} INTERFACE)
    else()
        add_library(${target_name} ${lib_type} ${EXOV6_LIB_SOURCES})
    endif()
    
    # Apply common configurations
    if(NOT lib_type STREQUAL "INTERFACE")
        exov6_apply_common_options(${target_name})
        exov6_configure_llvm_features(${target_name})
        exov6_configure_features(${target_name})
    endif()
    
    # Set include directories
    if(EXOV6_LIB_INCLUDES)
        if(lib_type STREQUAL "INTERFACE")
            target_include_directories(${target_name} INTERFACE ${EXOV6_LIB_INCLUDES})
        else()
            target_include_directories(${target_name} PUBLIC ${EXOV6_LIB_INCLUDES})
        endif()
    endif()
    
    # Set dependencies
    if(EXOV6_LIB_DEPENDENCIES)
        target_link_libraries(${target_name} PUBLIC ${EXOV6_LIB_DEPENDENCIES})
    endif()
    
    # Set definitions
    if(EXOV6_LIB_DEFINITIONS)
        if(lib_type STREQUAL "INTERFACE")
            target_compile_definitions(${target_name} INTERFACE ${EXOV6_LIB_DEFINITIONS})
        else()
            target_compile_definitions(${target_name} PUBLIC ${EXOV6_LIB_DEFINITIONS})
        endif()
    endif()
    
    # Set properties for non-interface libraries
    if(NOT lib_type STREQUAL "INTERFACE")
        set_target_properties(${target_name} PROPERTIES
            POSITION_INDEPENDENT_CODE OFF
            PREFIX "libexov6-"
        )
    endif()
endfunction()

# Create an ExoV6 executable target with all configurations
function(exov6_add_executable target_name)
    cmake_parse_arguments(EXOV6_EXE "" "" "SOURCES;INCLUDES;DEPENDENCIES;DEFINITIONS" ${ARGN})
    
    add_executable(${target_name} ${EXOV6_EXE_SOURCES})
    
    # Apply common configurations
    exov6_apply_common_options(${target_name})
    exov6_configure_llvm_features(${target_name})
    exov6_configure_features(${target_name})
    
    # Set include directories
    if(EXOV6_EXE_INCLUDES)
        target_include_directories(${target_name} PRIVATE ${EXOV6_EXE_INCLUDES})
    endif()
    
    # Set dependencies
    if(EXOV6_EXE_DEPENDENCIES)
        target_link_libraries(${target_name} PRIVATE ${EXOV6_EXE_DEPENDENCIES})
    endif()
    
    # Set definitions
    if(EXOV6_EXE_DEFINITIONS)
        target_compile_definitions(${target_name} PRIVATE ${EXOV6_EXE_DEFINITIONS})
    endif()
    
    # Set properties
    set_target_properties(${target_name} PROPERTIES
        PREFIX "exov6-"
    )
endfunction()

# Export configuration
set(EXOV6_CMAKE_DIR "${CMAKE_CURRENT_LIST_DIR}")
set(EXOV6_INCLUDE_DIRS 
    "${CMAKE_SOURCE_DIR}/include"
    "${CMAKE_SOURCE_DIR}/kernel/include"
    "${CMAKE_SOURCE_DIR}/proto"
)
# FindLLVMTools.cmake - Find LLVM toolchain components

# Find LLVM tools with proper version handling
function(find_llvm_tools)
    # Look for LLVM version 18 first, then fall back to unversioned
    set(LLVM_VERSION_SUFFIXES "-18" "")
    
    foreach(suffix ${LLVM_VERSION_SUFFIXES})
        find_program(LLVM_CONFIG NAMES llvm-config${suffix})
        if(LLVM_CONFIG)
            break()
        endif()
    endforeach()
    
    if(LLVM_CONFIG)
        execute_process(
            COMMAND ${LLVM_CONFIG} --version
            OUTPUT_VARIABLE LLVM_VERSION_STRING
            OUTPUT_STRIP_TRAILING_WHITESPACE
        )
        message(STATUS "Found LLVM version: ${LLVM_VERSION_STRING}")
        
        # Extract major version for suffix
        string(REGEX MATCH "^([0-9]+)" LLVM_MAJOR_VERSION ${LLVM_VERSION_STRING})
        set(VERSION_SUFFIX "-${LLVM_MAJOR_VERSION}")
    else()
        set(VERSION_SUFFIX "")
    endif()
    
    # Find individual tools
    find_program(LLVM_AR NAMES llvm-ar${VERSION_SUFFIX} llvm-ar)
    find_program(LLVM_NM NAMES llvm-nm${VERSION_SUFFIX} llvm-nm)
    find_program(LLVM_OBJCOPY NAMES llvm-objcopy${VERSION_SUFFIX} llvm-objcopy)
    find_program(LLVM_OBJDUMP NAMES llvm-objdump${VERSION_SUFFIX} llvm-objdump)
    find_program(LLVM_STRIP NAMES llvm-strip${VERSION_SUFFIX} llvm-strip)
    find_program(LLVM_RANLIB NAMES llvm-ranlib${VERSION_SUFFIX} llvm-ranlib)
    find_program(LLVM_OPT NAMES opt${VERSION_SUFFIX} opt)
    find_program(LLVM_LLC NAMES llc${VERSION_SUFFIX} llc)
    find_program(LLD NAMES ld.lld${VERSION_SUFFIX} ld.lld lld)
    
    # Set variables in parent scope
    set(LLVM_CONFIG ${LLVM_CONFIG} PARENT_SCOPE)
    set(LLVM_VERSION_STRING ${LLVM_VERSION_STRING} PARENT_SCOPE)
    set(LLVM_AR ${LLVM_AR} PARENT_SCOPE)
    set(LLVM_NM ${LLVM_NM} PARENT_SCOPE)
    set(LLVM_OBJCOPY ${LLVM_OBJCOPY} PARENT_SCOPE)
    set(LLVM_OBJDUMP ${LLVM_OBJDUMP} PARENT_SCOPE)
    set(LLVM_STRIP ${LLVM_STRIP} PARENT_SCOPE)
    set(LLVM_RANLIB ${LLVM_RANLIB} PARENT_SCOPE)
    set(LLVM_OPT ${LLVM_OPT} PARENT_SCOPE)
    set(LLVM_LLC ${LLVM_LLC} PARENT_SCOPE)
    set(LLD ${LLD} PARENT_SCOPE)
    
    # Determine if we found a complete toolchain
    if(LLVM_AR AND LLVM_OBJCOPY AND LLVM_STRIP)
        set(LLVM_TOOLS_FOUND TRUE PARENT_SCOPE)
    else()
        set(LLVM_TOOLS_FOUND FALSE PARENT_SCOPE)
    endif()
endfunction()

# Configure CMake to use LLVM tools
function(use_llvm_tools)
    find_llvm_tools()
    
    if(LLVM_TOOLS_FOUND)
        if(LLVM_AR)
            set(CMAKE_AR ${LLVM_AR} PARENT_SCOPE)
            message(STATUS "Using LLVM archiver: ${LLVM_AR}")
        endif()
        
        if(LLVM_RANLIB)
            set(CMAKE_RANLIB ${LLVM_RANLIB} PARENT_SCOPE)
            message(STATUS "Using LLVM ranlib: ${LLVM_RANLIB}")
        endif()
        
        if(LLVM_OBJCOPY)
            set(CMAKE_OBJCOPY ${LLVM_OBJCOPY} PARENT_SCOPE)
        endif()
        
        if(LLVM_STRIP)
            set(CMAKE_STRIP ${LLVM_STRIP} PARENT_SCOPE)
        endif()
        
        if(LLVM_OBJDUMP)
            set(CMAKE_OBJDUMP ${LLVM_OBJDUMP} PARENT_SCOPE)
        endif()
        
        if(LLVM_NM)
            set(CMAKE_NM ${LLVM_NM} PARENT_SCOPE)
        endif()
    else()
        message(WARNING "Complete LLVM toolchain not found")
    endif()
endfunction()

# Check if LLD is available
function(check_lld_availability)
    find_llvm_tools()
    
    if(LLD)
        set(LLD_AVAILABLE TRUE PARENT_SCOPE)
        message(STATUS "LLD linker found: ${LLD}")
    else()
        set(LLD_AVAILABLE FALSE PARENT_SCOPE)
        message(WARNING "LLD linker not found")
    endif()
endfunction()

# Check if Polly is available
function(check_polly_availability)
    find_llvm_tools()
    
    if(LLVM_OPT)
        # Try to run opt with polly to see if it's available
        execute_process(
            COMMAND ${LLVM_OPT} -help
            OUTPUT_VARIABLE OPT_HELP
            ERROR_QUIET
        )
        
        string(FIND "${OPT_HELP}" "polly" POLLY_FOUND)
        if(POLLY_FOUND GREATER -1)
            set(POLLY_AVAILABLE TRUE PARENT_SCOPE)
            message(STATUS "Polly optimizations available")
        else()
            set(POLLY_AVAILABLE FALSE PARENT_SCOPE)
            message(WARNING "Polly optimizations not available")
        endif()
    else()
        set(POLLY_AVAILABLE FALSE PARENT_SCOPE)
        message(WARNING "LLVM opt tool not found, Polly unavailable")
    endif()
endfunction()

# Main execution
if(CMAKE_C_COMPILER_ID MATCHES "Clang")
    find_llvm_tools()
    
    # Report found tools
    if(LLVM_CONFIG)
        message(STATUS "LLVM Config: ${LLVM_CONFIG}")
    endif()
    if(LLVM_AR)
        message(STATUS "LLVM AR: ${LLVM_AR}")
    endif()
    if(LLVM_OPT)
        message(STATUS "LLVM Opt: ${LLVM_OPT}")
    endif()
    if(LLD)
        message(STATUS "LLD: ${LLD}")
    endif()
else()
    message(STATUS "Non-Clang compiler detected, LLVM tools search skipped")
endif()
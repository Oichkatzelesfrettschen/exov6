# ═══════════════════════════════════════════════════════════════════════════════
# FeuerBird Exokernel - CCache Configuration Module
# Accelerates rebuilds by caching compilation results
# ═══════════════════════════════════════════════════════════════════════════════

option(ENABLE_CCACHE "Enable ccache for faster rebuilds" ON)

if(ENABLE_CCACHE)
    find_program(CCACHE_EXECUTABLE
        NAMES ccache
        DOC "Path to ccache executable"
    )
    
    if(CCACHE_EXECUTABLE)
        message(STATUS "ccache found: ${CCACHE_EXECUTABLE}")
        
        # Set ccache as compiler launcher
        set(CMAKE_C_COMPILER_LAUNCHER "${CCACHE_EXECUTABLE}")
        set(CMAKE_CXX_COMPILER_LAUNCHER "${CCACHE_EXECUTABLE}")
        
        # Configure ccache for optimal performance
        execute_process(COMMAND ${CCACHE_EXECUTABLE} --set-config=max_size=5G)
        execute_process(COMMAND ${CCACHE_EXECUTABLE} --set-config=compression=true)
        execute_process(COMMAND ${CCACHE_EXECUTABLE} --set-config=compression_level=6)
        execute_process(COMMAND ${CCACHE_EXECUTABLE} --set-config=sloppiness=pch_defines,time_macros)
        
        # Get ccache statistics
        execute_process(
            COMMAND ${CCACHE_EXECUTABLE} --show-stats
            OUTPUT_VARIABLE CCACHE_STATS
            OUTPUT_STRIP_TRAILING_WHITESPACE
        )
        
        message(STATUS "ccache enabled and configured")
        message(STATUS "  Max cache size: 5GB")
        message(STATUS "  Compression: enabled (level 6)")
        
        # Add ccache management targets
        add_custom_target(ccache-stats
            COMMAND ${CCACHE_EXECUTABLE} --show-stats
            COMMENT "Displaying ccache statistics"
        )
        
        add_custom_target(ccache-zero
            COMMAND ${CCACHE_EXECUTABLE} --zero-stats
            COMMENT "Zeroing ccache statistics"
        )
        
        add_custom_target(ccache-clean
            COMMAND ${CCACHE_EXECUTABLE} --clear
            COMMENT "Clearing ccache"
        )
        
        add_custom_target(ccache-info
            COMMAND ${CMAKE_COMMAND} -E echo "═══════════════════════════════════════"
            COMMAND ${CMAKE_COMMAND} -E echo "CCache Information"
            COMMAND ${CMAKE_COMMAND} -E echo "═══════════════════════════════════════"
            COMMAND ${CCACHE_EXECUTABLE} --version
            COMMAND ${CMAKE_COMMAND} -E echo ""
            COMMAND ${CMAKE_COMMAND} -E echo "Configuration:"
            COMMAND ${CCACHE_EXECUTABLE} --show-config
            COMMAND ${CMAKE_COMMAND} -E echo ""
            COMMAND ${CMAKE_COMMAND} -E echo "Statistics:"
            COMMAND ${CCACHE_EXECUTABLE} --show-stats
            COMMAND ${CMAKE_COMMAND} -E echo "═══════════════════════════════════════"
            COMMENT "Displaying ccache information"
        )
    else()
        message(STATUS "ccache not found, compilation cache disabled")
    endif()
else()
    message(STATUS "ccache disabled by user configuration")
endif()

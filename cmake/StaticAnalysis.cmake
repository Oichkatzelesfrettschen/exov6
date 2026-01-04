# ═══════════════════════════════════════════════════════════════════════════════
# FeuerBird Exokernel - Static Analysis Configuration Module
# Integrates multiple static analysis tools into the build system
# ═══════════════════════════════════════════════════════════════════════════════

option(ENABLE_STATIC_ANALYSIS "Enable static analysis tools" OFF)
option(ENABLE_CLANG_TIDY "Enable clang-tidy checks during build" OFF)
option(ENABLE_CPPCHECK "Enable cppcheck analysis" OFF)
option(ENABLE_IWYU "Enable include-what-you-use analysis" OFF)

# ─────────────────────────────────────────────────────────────────────────────────
# Clang-Tidy Configuration
# ─────────────────────────────────────────────────────────────────────────────────
if(ENABLE_CLANG_TIDY OR ENABLE_STATIC_ANALYSIS)
    find_program(CLANG_TIDY_EXECUTABLE
        NAMES clang-tidy clang-tidy-18 clang-tidy-17 clang-tidy-16
        DOC "Path to clang-tidy executable"
    )
    
    if(CLANG_TIDY_EXECUTABLE)
        message(STATUS "clang-tidy found: ${CLANG_TIDY_EXECUTABLE}")
        
        # Use .clang-tidy config file if it exists
        if(EXISTS "${CMAKE_SOURCE_DIR}/.clang-tidy")
            set(CMAKE_C_CLANG_TIDY "${CLANG_TIDY_EXECUTABLE}")
            set(CMAKE_CXX_CLANG_TIDY "${CLANG_TIDY_EXECUTABLE}")
            message(STATUS "clang-tidy enabled with config: ${CMAKE_SOURCE_DIR}/.clang-tidy")
        else()
            message(WARNING ".clang-tidy config file not found, skipping clang-tidy")
        endif()
        
        # Add manual clang-tidy target
        add_custom_target(clang-tidy
            COMMAND ${CMAKE_COMMAND} -E echo "Running clang-tidy on all source files..."
            COMMAND find ${CMAKE_SOURCE_DIR}/kernel ${CMAKE_SOURCE_DIR}/libos ${CMAKE_SOURCE_DIR}/src 
                -name "*.c" -o -name "*.cpp" -o -name "*.h" | 
                xargs ${CLANG_TIDY_EXECUTABLE} -p ${CMAKE_BINARY_DIR}
            WORKING_DIRECTORY ${CMAKE_SOURCE_DIR}
            COMMENT "Running clang-tidy static analysis"
        )
    else()
        message(WARNING "clang-tidy not found, static analysis disabled")
    endif()
endif()

# ─────────────────────────────────────────────────────────────────────────────────
# CppCheck Configuration
# ─────────────────────────────────────────────────────────────────────────────────
if(ENABLE_CPPCHECK OR ENABLE_STATIC_ANALYSIS)
    find_program(CPPCHECK_EXECUTABLE
        NAMES cppcheck
        DOC "Path to cppcheck executable"
    )
    
    if(CPPCHECK_EXECUTABLE)
        message(STATUS "cppcheck found: ${CPPCHECK_EXECUTABLE}")
        
        # Cppcheck configuration
        set(CPPCHECK_ARGS
            --enable=warning,style,performance,portability,information
            --suppress=missingIncludeSystem
            --suppress=unmatchedSuppression
            --inline-suppr
            --std=c17
            --platform=unix64
            --max-ctu-depth=4
            --check-level=exhaustive
            --inconclusive
            --force
            --xml
            --xml-version=2
        )
        
        add_custom_target(cppcheck
            COMMAND ${CPPCHECK_EXECUTABLE}
                ${CPPCHECK_ARGS}
                -I ${CMAKE_SOURCE_DIR}/include
                -I ${CMAKE_SOURCE_DIR}/kernel/include
                -I ${CMAKE_SOURCE_DIR}/libos
                ${CMAKE_SOURCE_DIR}/kernel
                ${CMAKE_SOURCE_DIR}/libos
                ${CMAKE_SOURCE_DIR}/src
                2> ${CMAKE_BINARY_DIR}/cppcheck-report.xml
            COMMAND ${CMAKE_COMMAND} -E echo "Cppcheck report saved to: ${CMAKE_BINARY_DIR}/cppcheck-report.xml"
            WORKING_DIRECTORY ${CMAKE_SOURCE_DIR}
            COMMENT "Running cppcheck static analysis"
        )
        
        # Human-readable cppcheck report
        add_custom_target(cppcheck-text
            COMMAND ${CPPCHECK_EXECUTABLE}
                ${CPPCHECK_ARGS}
                --template=gcc
                -I ${CMAKE_SOURCE_DIR}/include
                -I ${CMAKE_SOURCE_DIR}/kernel/include
                -I ${CMAKE_SOURCE_DIR}/libos
                ${CMAKE_SOURCE_DIR}/kernel
                ${CMAKE_SOURCE_DIR}/libos
                ${CMAKE_SOURCE_DIR}/src
                2> ${CMAKE_BINARY_DIR}/cppcheck-report.txt
            COMMAND ${CMAKE_COMMAND} -E echo "Cppcheck text report saved to: ${CMAKE_BINARY_DIR}/cppcheck-report.txt"
            WORKING_DIRECTORY ${CMAKE_SOURCE_DIR}
            COMMENT "Running cppcheck with text output"
        )
    else()
        message(WARNING "cppcheck not found")
    endif()
endif()

# ─────────────────────────────────────────────────────────────────────────────────
# Include-What-You-Use (IWYU) Configuration
# ─────────────────────────────────────────────────────────────────────────────────
if(ENABLE_IWYU OR ENABLE_STATIC_ANALYSIS)
    find_program(IWYU_EXECUTABLE
        NAMES include-what-you-use iwyu
        DOC "Path to include-what-you-use executable"
    )
    
    if(IWYU_EXECUTABLE)
        message(STATUS "include-what-you-use found: ${IWYU_EXECUTABLE}")
        
        # IWYU can be integrated into the build
        set(CMAKE_C_INCLUDE_WHAT_YOU_USE "${IWYU_EXECUTABLE};-Xiwyu;--no_fwd_decls;-Xiwyu;--verbose=1")
        
        # Manual IWYU target
        add_custom_target(iwyu
            COMMAND ${CMAKE_COMMAND} -E echo "Running include-what-you-use..."
            COMMAND find ${CMAKE_SOURCE_DIR}/kernel ${CMAKE_SOURCE_DIR}/libos ${CMAKE_SOURCE_DIR}/src 
                -name "*.c" | 
                xargs -I {} ${IWYU_EXECUTABLE} {} -Xiwyu --no_fwd_decls 
                -- -I${CMAKE_SOURCE_DIR}/include
            WORKING_DIRECTORY ${CMAKE_SOURCE_DIR}
            COMMENT "Running include-what-you-use analysis"
        )
    else()
        message(WARNING "include-what-you-use not found")
    endif()
endif()

# ─────────────────────────────────────────────────────────────────────────────────
# Unified static analysis target
# ─────────────────────────────────────────────────────────────────────────────────
if(ENABLE_STATIC_ANALYSIS)
    set(STATIC_ANALYSIS_TARGETS "")
    
    if(TARGET clang-tidy)
        list(APPEND STATIC_ANALYSIS_TARGETS clang-tidy)
    endif()
    
    if(TARGET cppcheck)
        list(APPEND STATIC_ANALYSIS_TARGETS cppcheck)
    endif()
    
    if(TARGET iwyu)
        list(APPEND STATIC_ANALYSIS_TARGETS iwyu)
    endif()
    
    if(STATIC_ANALYSIS_TARGETS)
        add_custom_target(static-analysis
            DEPENDS ${STATIC_ANALYSIS_TARGETS}
            COMMENT "Running all static analysis tools"
        )
        
        message(STATUS "Static analysis targets available:")
        foreach(target ${STATIC_ANALYSIS_TARGETS})
            message(STATUS "  - ${target}")
        endforeach()
        message(STATUS "  - static-analysis: Run all analysis tools")
    endif()
endif()

# ─────────────────────────────────────────────────────────────────────────────────
# Analysis report summary target
# ─────────────────────────────────────────────────────────────────────────────────
add_custom_target(analysis-summary
    COMMAND ${CMAKE_COMMAND} -E echo "═══════════════════════════════════════════"
    COMMAND ${CMAKE_COMMAND} -E echo "Static Analysis Summary"
    COMMAND ${CMAKE_COMMAND} -E echo "═══════════════════════════════════════════"
    COMMAND ${CMAKE_COMMAND} -E echo ""
    COMMAND ${CMAKE_COMMAND} -E echo "Available analysis tools:"
    COMMAND ${CMAKE_COMMAND} -E echo "  clang-tidy: ${CLANG_TIDY_EXECUTABLE}"
    COMMAND ${CMAKE_COMMAND} -E echo "  cppcheck:   ${CPPCHECK_EXECUTABLE}"
    COMMAND ${CMAKE_COMMAND} -E echo "  iwyu:       ${IWYU_EXECUTABLE}"
    COMMAND ${CMAKE_COMMAND} -E echo ""
    COMMAND ${CMAKE_COMMAND} -E echo "Run 'ninja static-analysis' to analyze code"
    COMMAND ${CMAKE_COMMAND} -E echo "═══════════════════════════════════════════"
    COMMENT "Displaying static analysis summary"
)

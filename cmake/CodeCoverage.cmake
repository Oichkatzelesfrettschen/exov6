# ═══════════════════════════════════════════════════════════════════════════════
# FeuerBird Exokernel - Code Coverage Configuration Module
# Provides comprehensive code coverage support using LLVM and GCC tools
# ═══════════════════════════════════════════════════════════════════════════════

# Coverage option
option(ENABLE_COVERAGE "Enable code coverage instrumentation" OFF)

if(ENABLE_COVERAGE)
    message(STATUS "Code coverage enabled")
    
    # Detect compiler
    if(CMAKE_C_COMPILER_ID MATCHES "Clang")
        message(STATUS "Using LLVM coverage tools (llvm-cov, llvm-profdata)")
        
        # LLVM coverage flags
        set(COVERAGE_C_FLAGS "-fprofile-instr-generate -fcoverage-mapping")
        set(COVERAGE_CXX_FLAGS "-fprofile-instr-generate -fcoverage-mapping")
        set(COVERAGE_LINKER_FLAGS "-fprofile-instr-generate -fcoverage-mapping")
        
        # Find LLVM coverage tools
        find_program(LLVM_COV_EXECUTABLE
            NAMES llvm-cov llvm-cov-18 llvm-cov-17 llvm-cov-16
            DOC "LLVM coverage tool"
        )
        
        find_program(LLVM_PROFDATA_EXECUTABLE
            NAMES llvm-profdata llvm-profdata-18 llvm-profdata-17 llvm-profdata-16
            DOC "LLVM profile data tool"
        )
        
        if(LLVM_COV_EXECUTABLE AND LLVM_PROFDATA_EXECUTABLE)
            set(COVERAGE_TOOLS_FOUND TRUE)
            message(STATUS "  llvm-cov: ${LLVM_COV_EXECUTABLE}")
            message(STATUS "  llvm-profdata: ${LLVM_PROFDATA_EXECUTABLE}")
        else()
            message(WARNING "LLVM coverage tools not found")
            set(COVERAGE_TOOLS_FOUND FALSE)
        endif()
        
    elseif(CMAKE_C_COMPILER_ID MATCHES "GNU")
        message(STATUS "Using GCC coverage tools (gcov, lcov)")
        
        # GCC coverage flags
        set(COVERAGE_C_FLAGS "-fprofile-arcs -ftest-coverage")
        set(COVERAGE_CXX_FLAGS "-fprofile-arcs -ftest-coverage")
        set(COVERAGE_LINKER_FLAGS "-fprofile-arcs -ftest-coverage")
        
        # Find GCC coverage tools
        find_program(GCOV_EXECUTABLE
            NAMES gcov gcov-11 gcov-12 gcov-13
            DOC "GCC coverage tool"
        )
        
        find_program(LCOV_EXECUTABLE
            NAMES lcov
            DOC "LCOV coverage tool"
        )
        
        find_program(GENHTML_EXECUTABLE
            NAMES genhtml
            DOC "LCOV HTML generator"
        )
        
        if(GCOV_EXECUTABLE AND LCOV_EXECUTABLE AND GENHTML_EXECUTABLE)
            set(COVERAGE_TOOLS_FOUND TRUE)
            message(STATUS "  gcov: ${GCOV_EXECUTABLE}")
            message(STATUS "  lcov: ${LCOV_EXECUTABLE}")
            message(STATUS "  genhtml: ${GENHTML_EXECUTABLE}")
        else()
            message(WARNING "GCC coverage tools not found")
            set(COVERAGE_TOOLS_FOUND FALSE)
        endif()
    else()
        message(WARNING "Code coverage not supported for compiler: ${CMAKE_C_COMPILER_ID}")
        set(COVERAGE_TOOLS_FOUND FALSE)
    endif()
    
    # Apply coverage flags if tools found
    if(COVERAGE_TOOLS_FOUND)
        set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} ${COVERAGE_C_FLAGS}")
        set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} ${COVERAGE_CXX_FLAGS}")
        set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} ${COVERAGE_LINKER_FLAGS}")
        set(CMAKE_SHARED_LINKER_FLAGS "${CMAKE_SHARED_LINKER_FLAGS} ${COVERAGE_LINKER_FLAGS}")
        
        # Coverage targets
        if(CMAKE_C_COMPILER_ID MATCHES "Clang")
            # LLVM coverage targets
            add_custom_target(coverage-clean
                COMMAND ${CMAKE_COMMAND} -E remove_directory ${CMAKE_BINARY_DIR}/coverage
                COMMAND ${CMAKE_COMMAND} -E make_directory ${CMAKE_BINARY_DIR}/coverage
                COMMAND find ${CMAKE_BINARY_DIR} -name "*.profraw" -delete
                COMMENT "Cleaning coverage data"
            )
            
            add_custom_target(coverage-merge
                COMMAND ${LLVM_PROFDATA_EXECUTABLE} merge -sparse 
                    ${CMAKE_BINARY_DIR}/**/*.profraw 
                    -o ${CMAKE_BINARY_DIR}/coverage/merged.profdata
                DEPENDS coverage-clean
                COMMENT "Merging LLVM coverage data"
            )
            
            add_custom_target(coverage-report
                COMMAND ${LLVM_COV_EXECUTABLE} report 
                    -instr-profile=${CMAKE_BINARY_DIR}/coverage/merged.profdata
                    -object ${CMAKE_BINARY_DIR}/kernel
                DEPENDS coverage-merge
                COMMENT "Generating LLVM coverage report"
            )
            
            add_custom_target(coverage-html
                COMMAND ${LLVM_COV_EXECUTABLE} show 
                    -instr-profile=${CMAKE_BINARY_DIR}/coverage/merged.profdata
                    -object ${CMAKE_BINARY_DIR}/kernel
                    -format=html
                    -output-dir=${CMAKE_BINARY_DIR}/coverage/html
                DEPENDS coverage-merge
                COMMENT "Generating LLVM HTML coverage report at coverage/html/index.html"
            )
            
            add_custom_target(coverage
                DEPENDS coverage-html
                COMMENT "Full LLVM coverage analysis complete"
            )
            
        elseif(CMAKE_C_COMPILER_ID MATCHES "GNU")
            # GCC/LCOV coverage targets
            add_custom_target(coverage-clean
                COMMAND ${CMAKE_COMMAND} -E remove_directory ${CMAKE_BINARY_DIR}/coverage
                COMMAND ${CMAKE_COMMAND} -E make_directory ${CMAKE_BINARY_DIR}/coverage
                COMMAND find ${CMAKE_BINARY_DIR} -name "*.gcda" -delete
                COMMENT "Cleaning coverage data"
            )
            
            add_custom_target(coverage-capture
                COMMAND ${LCOV_EXECUTABLE} 
                    --capture 
                    --directory ${CMAKE_BINARY_DIR}
                    --output-file ${CMAKE_BINARY_DIR}/coverage/coverage.info
                    --gcov-tool ${GCOV_EXECUTABLE}
                DEPENDS coverage-clean
                COMMENT "Capturing GCC coverage data"
            )
            
            add_custom_target(coverage-filter
                COMMAND ${LCOV_EXECUTABLE}
                    --remove ${CMAKE_BINARY_DIR}/coverage/coverage.info
                    '/usr/*' '*/tests/*' '*/demos/*'
                    --output-file ${CMAKE_BINARY_DIR}/coverage/coverage-filtered.info
                DEPENDS coverage-capture
                COMMENT "Filtering coverage data"
            )
            
            add_custom_target(coverage-html
                COMMAND ${GENHTML_EXECUTABLE}
                    ${CMAKE_BINARY_DIR}/coverage/coverage-filtered.info
                    --output-directory ${CMAKE_BINARY_DIR}/coverage/html
                DEPENDS coverage-filter
                COMMENT "Generating GCC HTML coverage report at coverage/html/index.html"
            )
            
            add_custom_target(coverage-report
                COMMAND ${LCOV_EXECUTABLE}
                    --list ${CMAKE_BINARY_DIR}/coverage/coverage-filtered.info
                DEPENDS coverage-filter
                COMMENT "Generating GCC coverage summary"
            )
            
            add_custom_target(coverage
                DEPENDS coverage-html
                COMMENT "Full GCC coverage analysis complete"
            )
        endif()
        
        message(STATUS "Coverage targets available:")
        message(STATUS "  - coverage-clean: Clean coverage data")
        message(STATUS "  - coverage-report: Generate text coverage report")
        message(STATUS "  - coverage-html: Generate HTML coverage report")
        message(STATUS "  - coverage: Run full coverage analysis")
    endif()
endif()

# Export variables for subdirectories (only if we have a parent scope)
if(NOT CMAKE_SOURCE_DIR STREQUAL CMAKE_CURRENT_SOURCE_DIR)
    set(COVERAGE_ENABLED ${ENABLE_COVERAGE} PARENT_SCOPE)
else()
    set(COVERAGE_ENABLED ${ENABLE_COVERAGE})
endif()

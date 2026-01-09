# FeuerBird - Run clang-tidy analysis in CI mode (strict error checking)
# This script is invoked by cmake -P and fails on errors

find_program(CLANG_TIDY_EXECUTABLE
    NAMES clang-tidy clang-tidy-18 clang-tidy-17 clang-tidy-16
)

if(NOT CLANG_TIDY_EXECUTABLE)
    message(FATAL_ERROR "clang-tidy not found")
endif()

# Source and output directories
set(SOURCE_DIRS
    "${CMAKE_SOURCE_DIR}/kernel"
    "${CMAKE_SOURCE_DIR}/libos"
    "${CMAKE_SOURCE_DIR}/src"
    "${CMAKE_SOURCE_DIR}/include"
)

set(REPORT_FILE "${CMAKE_BINARY_DIR}/reports/clang-tidy-ci-report.txt")

# Run clang-tidy with compilation database
message(STATUS "Running clang-tidy in CI mode (strict error checking)...")
message(STATUS "Compilation database: ${CMAKE_BINARY_DIR}/compile_commands.json")

# Execute clang-tidy with error reporting
execute_process(
    COMMAND bash -c "
        ERRORS=0
        for dir in ${SOURCE_DIRS}; do
            find \$dir -type f \\( -name '*.c' -o -name '*.cpp' -o -name '*.h' \\) \\
                ! -path '*/test/*' ! -path '*/demo/*'
        done | sort -u | while read file; do
            OUTPUT=\$(\"\${CLANG_TIDY_EXECUTABLE}\" -p \"${CMAKE_BINARY_DIR}\" \"\$file\" 2>&1)
            if echo \"\$OUTPUT\" | grep -q 'error:'; then
                echo \"\$OUTPUT\" >> \"${REPORT_FILE}\"
                ERRORS=\$((ERRORS + 1))
            fi
        done
        exit \$ERRORS
    "
    RESULT_VARIABLE CLANG_TIDY_RESULT
)

# Generate summary report
execute_process(
    COMMAND bash -c "
        {
            echo '═══════════════════════════════════════════'
            echo 'clang-tidy CI Analysis Report'
            echo '═══════════════════════════════════════════'
            echo ''
            if [ -f '${REPORT_FILE}' ]; then
                ERROR_COUNT=\$(grep -c 'error:' '${REPORT_FILE}' || echo 0)
                echo \"Critical Errors: \$ERROR_COUNT\"
                echo ''
                echo 'Error Details:'
                cat '${REPORT_FILE}'
            else
                echo 'No clang-tidy errors found!'
            fi
            echo ''
            echo '═══════════════════════════════════════════'
        }
    "
)

# Fail CI if errors were found
if(CLANG_TIDY_RESULT GREATER 0)
    message(FATAL_ERROR "clang-tidy found ${CLANG_TIDY_RESULT} files with errors. See ${REPORT_FILE}")
else()
    message(STATUS "clang-tidy analysis passed with no errors")
endif()

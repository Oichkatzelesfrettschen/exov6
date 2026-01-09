# FeuerBird - Run clang-tidy analysis with report generation
# This script is invoked by cmake -P and generates a clang-tidy report

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
)

set(REPORT_FILE "${CMAKE_BINARY_DIR}/reports/clang-tidy-report.txt")

# Run clang-tidy with compilation database
message(STATUS "Running clang-tidy analysis...")
message(STATUS "Compilation database: ${CMAKE_BINARY_DIR}/compile_commands.json")
message(STATUS "Output report: ${REPORT_FILE}")

# Execute clang-tidy
execute_process(
    COMMAND bash -c "
        for dir in ${SOURCE_DIRS}; do
            find \$dir -type f \\( -name '*.c' -o -name '*.cpp' -o -name '*.h' \\) \\
                ! -path '*/test/*' ! -path '*/demo/*'
        done | sort -u | while read file; do
            echo \"Analyzing: \$file\"
            \"${CLANG_TIDY_EXECUTABLE}\" -p \"${CMAKE_BINARY_DIR}\" \"\$file\" 2>&1
        done
    "
    OUTPUT_FILE "${REPORT_FILE}"
    ERROR_FILE "${REPORT_FILE}"
)

# Check report and print summary
execute_process(
    COMMAND bash -c "
        echo '═══════════════════════════════════════════'
        echo 'clang-tidy Analysis Report'
        echo '═══════════════════════════════════════════'
        echo ''
        if [ -f '${REPORT_FILE}' ]; then
            ERROR_COUNT=\$(grep -c '^[^:]*:[0-9]*:[0-9]*: error:' '${REPORT_FILE}' || echo 0)
            WARNING_COUNT=\$(grep -c '^[^:]*:[0-9]*:[0-9]*: warning:' '${REPORT_FILE}' || echo 0)
            echo \"Errors:   \$ERROR_COUNT\"
            echo \"Warnings: \$WARNING_COUNT\"
            echo \"Report saved to: ${REPORT_FILE}\"
            if [ \$ERROR_COUNT -gt 0 ]; then
                echo ''
                echo 'First 10 errors:'
                grep '^[^:]*:[0-9]*:[0-9]*: error:' '${REPORT_FILE}' | head -10
            fi
        fi
        echo '═══════════════════════════════════════════'
    "
)

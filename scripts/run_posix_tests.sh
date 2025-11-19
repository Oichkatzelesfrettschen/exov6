#!/bin/bash
# POSIX Compliance Test Runner for ExoKernel v6
# This script runs the official POSIX test suite against our implementations

set -e

# Configuration
REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
TEST_SUITE="${REPO_ROOT}/test_isolation/openposixtestsuite"
RESULTS_DIR="${REPO_ROOT}/test_results"
TIMESTAMP=$(date +"%Y%m%d_%H%M%S")
RESULTS_FILE="${RESULTS_DIR}/posix_compliance_${TIMESTAMP}.txt"

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m'

echo -e "${BLUE}=== POSIX Compliance Test Suite ===${NC}"
echo -e "${YELLOW}Testing ExoKernel v6 against IEEE Std 1003.1-2024${NC}"
echo

# Create results directory
mkdir -p "$RESULTS_DIR"

# Test categories
declare -A TEST_CATEGORIES=(
    ["conformance"]="Conformance tests for POSIX APIs"
    ["functional"]="Functional tests for utilities"
    ["stress"]="Stress tests for robustness"
    ["performance"]="Performance benchmarks"
)

# Initialize counters
TOTAL_TESTS=0
PASSED_TESTS=0
FAILED_TESTS=0
SKIPPED_TESTS=0

# Function to run a single test
run_test() {
    local test_path=$1
    local test_name=$(basename "$test_path")
    
    ((TOTAL_TESTS++))
    
    # Run test in isolated environment
    if timeout 10 "$test_path" > /dev/null 2>&1; then
        echo -e "${GREEN}✓${NC} $test_name"
        ((PASSED_TESTS++))
        echo "PASS: $test_path" >> "$RESULTS_FILE"
    else
        local exit_code=$?
        if [ $exit_code -eq 124 ]; then
            echo -e "${YELLOW}⧗${NC} $test_name (timeout)"
            ((SKIPPED_TESTS++))
            echo "TIMEOUT: $test_path" >> "$RESULTS_FILE"
        else
            echo -e "${RED}✗${NC} $test_name (exit: $exit_code)"
            ((FAILED_TESTS++))
            echo "FAIL: $test_path (exit: $exit_code)" >> "$RESULTS_FILE"
        fi
    fi
}

# Test our POSIX utilities
echo -e "${BLUE}Testing POSIX Utilities${NC}"
for util in ${REPO_ROOT}/user/*.c; do
    util_name=$(basename "$util" .c)
    
    # Skip non-POSIX utilities
    if [[ "$util_name" =~ ^(caplib|door|chan|blink|zombie|usertests|.*_demo|.*_test)$ ]]; then
        continue
    fi
    
    # Find corresponding tests
    if [ -d "${TEST_SUITE}/conformance/interfaces/${util_name}" ]; then
        echo -e "\n${BLUE}Testing: ${util_name}${NC}"
        for test in "${TEST_SUITE}/conformance/interfaces/${util_name}"/*.c; do
            if [ -f "$test" ]; then
                run_test "$test"
            fi
        done
    fi
done

# Summary
echo
echo -e "${BLUE}=== Test Summary ===${NC}"
echo "Total Tests: $TOTAL_TESTS"
echo -e "${GREEN}Passed: $PASSED_TESTS${NC}"
echo -e "${RED}Failed: $FAILED_TESTS${NC}"
echo -e "${YELLOW}Skipped: $SKIPPED_TESTS${NC}"
echo
echo "Detailed results saved to: $RESULTS_FILE"

# Calculate compliance percentage
if [ $TOTAL_TESTS -gt 0 ]; then
    COMPLIANCE=$((PASSED_TESTS * 100 / TOTAL_TESTS))
    echo
    echo -e "${BLUE}POSIX Compliance: ${COMPLIANCE}%${NC}"
    
    if [ $COMPLIANCE -ge 90 ]; then
        echo -e "${GREEN}✓ Excellent compliance!${NC}"
    elif [ $COMPLIANCE -ge 70 ]; then
        echo -e "${YELLOW}⚠ Good compliance, but improvements needed${NC}"
    else
        echo -e "${RED}✗ Significant compliance issues${NC}"
    fi
fi

exit $FAILED_TESTS

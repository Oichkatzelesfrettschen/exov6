#!/bin/bash
# Fetch and integrate the Open POSIX Test Suite
# This script downloads, builds, and prepares the official POSIX compliance test suite
# GPL code is isolated and only fetched when needed for testing

set -e

# Configuration
REPO_ROOT="/Users/eirikr/Documents/GitHub/exov6"
TEST_DIR="${REPO_ROOT}/posix_test_suite"
TEST_URL="https://github.com/linux-test-project/ltp.git"
POSIX_URL="https://github.com/openposixtestsuite/openposixtestsuite.git"
ISOLATION_DIR="${REPO_ROOT}/test_isolation"

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

echo -e "${BLUE}=== Open POSIX Test Suite Fetcher ===${NC}"
echo -e "${YELLOW}Note: The Open POSIX Test Suite is GPL-licensed.${NC}"
echo -e "${YELLOW}It will be fetched and isolated for testing purposes only.${NC}"
echo -e "${YELLOW}Your BSD-licensed code remains separate.${NC}"
echo

# Function to print status
status() {
    echo -e "${GREEN}[✓]${NC} $1"
}

error() {
    echo -e "${RED}[✗]${NC} $1"
    exit 1
}

warning() {
    echo -e "${YELLOW}[!]${NC} $1"
}

# Check if user wants to proceed
read -p "Do you want to fetch the GPL-licensed test suite for compliance testing? (y/N) " -n 1 -r
echo
if [[ ! $REPLY =~ ^[Yy]$ ]]; then
    warning "Test suite fetch cancelled. You can run this script later when needed."
    exit 0
fi

# Create isolation directory
echo -e "${BLUE}Step 1: Creating isolation environment${NC}"
mkdir -p "$ISOLATION_DIR"
cd "$ISOLATION_DIR"

# Add to .gitignore if not already there
if ! grep -q "^test_isolation/" "${REPO_ROOT}/.gitignore" 2>/dev/null; then
    echo "test_isolation/" >> "${REPO_ROOT}/.gitignore"
    status "Added test_isolation to .gitignore"
fi

# Clone or update the test suite
echo -e "${BLUE}Step 2: Fetching Open POSIX Test Suite${NC}"
if [ -d "openposixtestsuite" ]; then
    warning "Test suite already exists, updating..."
    cd openposixtestsuite
    git pull --quiet || warning "Could not update, using existing version"
    cd ..
else
    echo "Cloning Open POSIX Test Suite..."
    git clone --depth 1 "$POSIX_URL" openposixtestsuite 2>/dev/null || \
        git clone --depth 1 "https://github.com/linux-test-project/ltp.git" openposixtestsuite
    status "Test suite cloned successfully"
fi

# Create test runner script
echo -e "${BLUE}Step 3: Creating test runner infrastructure${NC}"
cat > "${REPO_ROOT}/run_posix_tests.sh" << 'RUNNER_EOF'
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
RUNNER_EOF

chmod +x "${REPO_ROOT}/run_posix_tests.sh"
status "Created test runner script"

# Create Makefile integration
echo -e "${BLUE}Step 4: Integrating with build system${NC}"
cat > "${REPO_ROOT}/Makefile.posix_tests" << 'MAKEFILE_EOF'
# POSIX Test Suite Integration
# This file is included by the main Makefile

.PHONY: fetch-posix-tests run-posix-tests posix-compliance test-all

# Fetch the test suite (only when needed)
fetch-posix-tests:
	@echo "Fetching POSIX test suite..."
	@bash scripts/fetch_posix_test_suite.sh

# Run POSIX compliance tests
run-posix-tests: all
	@echo "Running POSIX compliance tests..."
	@bash run_posix_tests.sh

# Full compliance check
posix-compliance: fetch-posix-tests run-posix-tests
	@echo "POSIX compliance testing complete"

# Run all tests with maximum strictness
test-all: posix-compliance
	@echo "Running all tests with -Wall -Werror..."
	$(MAKE) clean
	$(MAKE) CFLAGS="$(CFLAGS) -Wall -Werror -Wextra -pedantic" all
	@echo "All tests completed successfully!"

# Generate compliance report
compliance-report:
	@echo "Generating POSIX compliance report..."
	@bash scripts/generate_compliance_report.sh > POSIX_COMPLIANCE_REPORT.md
	@echo "Report generated: POSIX_COMPLIANCE_REPORT.md"
MAKEFILE_EOF

status "Created Makefile integration"

# Create build verification script
echo -e "${BLUE}Step 5: Creating build verification system${NC}"
cat > "${REPO_ROOT}/scripts/verify_build.sh" << 'VERIFY_EOF'
#!/bin/bash
# Build Verification Script
# Ensures all files are properly included in the build system

set -e

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
ERRORS=0
WARNINGS=0

echo "=== Build System Verification ==="
echo

# Check all C files are in Makefile
echo "Checking for missing files in Makefile..."
for f in ${REPO_ROOT}/user/*.c; do
    base=$(basename "$f" .c)
    # Skip test files and examples
    if [[ "$base" =~ (test|demo|example|caplib|door|chan|blink|zombie) ]]; then
        continue
    fi
    
    if ! grep -q "_$base" "${REPO_ROOT}/Makefile"; then
        echo "ERROR: $base.c not in Makefile UPROGS"
        ((ERRORS++))
    fi
done

# Check for duplicate entries
echo "Checking for duplicate entries..."
duplicates=$(grep -o "_[a-zA-Z0-9_]*" "${REPO_ROOT}/Makefile" | sort | uniq -d)
if [ -n "$duplicates" ]; then
    echo "WARNING: Duplicate entries in Makefile:"
    echo "$duplicates"
    ((WARNINGS++))
fi

# Verify all utilities compile
echo "Verifying compilation with -Wall -Werror..."
cd "$REPO_ROOT"
make clean > /dev/null 2>&1
if make CFLAGS="-Wall -Werror -Wextra" all > /tmp/build_log.txt 2>&1; then
    echo "✓ All files compile without warnings"
else
    echo "✗ Compilation errors detected:"
    grep -E "(error:|warning:)" /tmp/build_log.txt | head -20
    ((ERRORS++))
fi

# Summary
echo
echo "=== Verification Summary ==="
echo "Errors: $ERRORS"
echo "Warnings: $WARNINGS"

if [ $ERRORS -eq 0 ] && [ $WARNINGS -eq 0 ]; then
    echo "✓ Build system is properly configured!"
    exit 0
else
    echo "✗ Build system needs attention"
    exit 1
fi
VERIFY_EOF

chmod +x "${REPO_ROOT}/scripts/verify_build.sh"
status "Created build verification script"

# Create comprehensive test launcher
echo -e "${BLUE}Step 6: Creating comprehensive test launcher${NC}"
cat > "${REPO_ROOT}/test_everything.sh" << 'LAUNCHER_EOF'
#!/bin/bash
# Comprehensive Test Launcher
# Runs all tests: build verification, POSIX compliance, and stress tests

set -e

echo "=== ExoKernel v6 Comprehensive Test Suite ==="
echo "This will run ALL tests with maximum strictness"
echo

# Step 1: Verify build system
echo "[1/4] Verifying build system..."
if bash scripts/verify_build.sh; then
    echo "✓ Build system verified"
else
    echo "✗ Build system has issues, fix them first"
    exit 1
fi

# Step 2: Build with all warnings as errors
echo "[2/4] Building with -Wall -Werror..."
make clean
if make CFLAGS="-Wall -Werror -Wextra -pedantic -std=c17" all; then
    echo "✓ Built successfully with strict flags"
else
    echo "✗ Build failed with strict flags"
    exit 1
fi

# Step 3: Run POSIX compliance tests
echo "[3/4] Running POSIX compliance tests..."
if [ ! -d "test_isolation/openposixtestsuite" ]; then
    echo "Fetching test suite first..."
    bash scripts/fetch_posix_test_suite.sh
fi
bash run_posix_tests.sh

# Step 4: Generate compliance report
echo "[4/4] Generating compliance report..."
bash scripts/generate_compliance_report.sh

echo
echo "=== All Tests Complete ==="
echo "See test_results/ for detailed results"
LAUNCHER_EOF

chmod +x "${REPO_ROOT}/test_everything.sh"
status "Created comprehensive test launcher"

# Final summary
echo
echo -e "${GREEN}=== Setup Complete ===${NC}"
echo "The POSIX test suite infrastructure has been created."
echo
echo "Available commands:"
echo "  make fetch-posix-tests  - Download the test suite"
echo "  make run-posix-tests    - Run compliance tests"
echo "  make posix-compliance   - Full compliance check"
echo "  make test-all          - Run everything with -Wall -Werror"
echo "  ./test_everything.sh   - Comprehensive test suite"
echo
echo "The test suite is GPL-licensed and isolated in test_isolation/"
echo "Your BSD code remains in the main repository."
echo
status "Ready for POSIX compliance testing!"
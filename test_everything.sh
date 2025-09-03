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

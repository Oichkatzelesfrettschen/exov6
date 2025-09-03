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

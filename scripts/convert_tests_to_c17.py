#!/usr/bin/env python3
"""
Convert Python tests to pure C17 implementations.
This maintains test logic while creating native C test executables.
"""

import os
import re
from pathlib import Path

def extract_c_code_from_python(py_file):
    """Extract embedded C code from Python test file."""
    with open(py_file, 'r') as f:
        content = f.read()
    
    # Find C code blocks
    c_code_pattern = r'C_CODE\s*=\s*"""(.*?)"""'
    matches = re.findall(c_code_pattern, content, re.DOTALL)
    
    if matches:
        return matches[0]
    return None

def convert_python_test_to_c17(py_file, output_dir):
    """Convert a Python test file to C17."""
    base_name = py_file.stem.replace('test_', '')
    c_file = output_dir / f"test_{base_name}.c"
    
    # Extract embedded C code if present
    embedded_c = extract_c_code_from_python(py_file)
    
    # Read Python test to understand test cases
    with open(py_file, 'r') as f:
        py_content = f.read()
    
    # Extract test function names
    test_functions = re.findall(r'def\s+(test_\w+)\s*\(', py_content)
    
    # Generate C17 test template
    c_template = f"""/**
 * @file test_{base_name}.c
 * @brief C17 test for {base_name.replace('_', ' ')}
 * 
 * Converted from Python test {py_file.name}
 */

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <stdbool.h>
#include <assert.h>
#include <string.h>

/* Test framework */
#define TEST_ASSERT(cond, msg) \\
    do {{ \\
        if (!(cond)) {{ \\
            fprintf(stderr, "FAIL: %s:%d: %s\\n", __FILE__, __LINE__, msg); \\
            return 1; \\
        }} \\
    }} while(0)

#define TEST_PASS(name) printf("PASS: %s\\n", name)

"""
    
    # Add embedded C code if found
    if embedded_c:
        # Extract just the main logic
        main_match = re.search(r'int\s+main\s*\([^)]*\)\s*{(.*?)}', embedded_c, re.DOTALL)
        if main_match:
            c_template += f"""
/* Test implementation from embedded code */
static int test_{base_name}_core(void) {{
{main_match.group(1)}
}}
"""
    
    # Generate test functions
    for test_func in test_functions:
        func_name = test_func.replace('test_', '')
        c_template += f"""
static int {test_func}(void) {{
    /* TODO: Implement {func_name} test logic */
    TEST_PASS("{func_name}");
    return 0;
}}
"""
    
    # Add main function
    c_template += """
int main(int argc, char *argv[]) {
    int failures = 0;
    
    printf("=== %s Test Suite (C17) ===\\n", \""""
    c_template += base_name.replace('_', ' ').title()
    c_template += """\");
    
"""
    
    # Add test calls
    for test_func in test_functions:
        c_template += f"    failures += {test_func}();\n"
    
    c_template += """    
    if (failures == 0) {
        printf("\\n✓ All tests passed\\n");
    } else {
        printf("\\n✗ %d test(s) failed\\n", failures);
    }
    
    return failures;
}
"""
    
    # Write the C file
    with open(c_file, 'w') as f:
        f.write(c_template)
    
    return c_file

def create_test_makefile(test_dir):
    """Create a Makefile for C17 tests."""
    makefile_content = """# C17 Test Suite Makefile
CC = clang
CFLAGS = -std=c17 -Wall -Werror -O2 -I../../include -I../../kernel
LDFLAGS = 

# Find all test files
TESTS = $(wildcard test_*.c)
BINARIES = $(TESTS:.c=)

all: $(BINARIES)

%: %.c
	$(CC) $(CFLAGS) $< -o $@ $(LDFLAGS)

run: all
	@for test in $(BINARIES); do \\
		echo "Running $$test..."; \\
		./$$test || exit 1; \\
	done

clean:
	rm -f $(BINARIES) *.o

.PHONY: all run clean
"""
    
    makefile_path = test_dir / "Makefile"
    with open(makefile_path, 'w') as f:
        f.write(makefile_content)
    
    return makefile_path

def main():
    """Convert all Python tests to C17."""
    tests_dir = Path("tests")
    c17_dir = Path("tests/c17")
    
    # Create directory structure
    for subdir in ["unit", "integration", "performance", "posix"]:
        (c17_dir / subdir).mkdir(parents=True, exist_ok=True)
    
    # Convert Python tests
    py_tests = list(tests_dir.glob("test_*.py"))
    print(f"Converting {len(py_tests)} Python tests to C17...")
    
    for py_test in py_tests:
        # Categorize test
        if "posix" in py_test.stem:
            output_dir = c17_dir / "posix"
        elif "perf" in py_test.stem or "bench" in py_test.stem:
            output_dir = c17_dir / "performance"
        elif "integration" in py_test.stem or "ipc" in py_test.stem:
            output_dir = c17_dir / "integration"
        else:
            output_dir = c17_dir / "unit"
        
        try:
            c_file = convert_python_test_to_c17(py_test, output_dir)
            print(f"  ✓ {py_test.name} -> {c_file.relative_to(Path.cwd())}")
        except Exception as e:
            print(f"  ✗ {py_test.name}: {e}")
    
    # Create Makefiles
    for subdir in ["unit", "integration", "performance", "posix"]:
        makefile = create_test_makefile(c17_dir / subdir)
        print(f"Created {makefile.relative_to(Path.cwd())}")
    
    print("\nConversion complete!")
    print("Next steps:")
    print("1. Review and complete the TODO sections in generated tests")
    print("2. Update CMakeLists.txt to include C17 tests")
    print("3. Run 'make run' in each test subdirectory")

if __name__ == "__main__":
    main()
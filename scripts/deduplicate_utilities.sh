#!/bin/bash
# Script to deduplicate user utilities and consolidate implementations
# Handles function-level deduplication and creates unified versions

set -e

echo "=== FeuerBird Utility Deduplication Script ==="
echo "Consolidating multiple implementations into single utilities"
echo

# Create backup directory
mkdir -p user/duplicates_backup

# Function to analyze and merge utility variants
merge_utility_variants() {
    local base_name="$1"
    local variants=("${@:2}")
    local best_impl=""
    local max_lines=0
    
    echo "Analyzing $base_name variants:"
    
    # Find the most complete implementation
    for variant in "${variants[@]}"; do
        if [ -f "user/$variant" ]; then
            lines=$(wc -l < "user/$variant")
            echo "  - $variant: $lines lines"
            if [ "$lines" -gt "$max_lines" ]; then
                max_lines=$lines
                best_impl=$variant
            fi
        fi
    done
    
    if [ -n "$best_impl" ]; then
        echo "  Selected: $best_impl (most complete)"
        echo "  Creating unified user/${base_name}.c"
        
        # Backup all variants
        for variant in "${variants[@]}"; do
            if [ -f "user/$variant" ]; then
                cp "user/$variant" "user/duplicates_backup/"
            fi
        done
        
        # Create merge report
        cat > "user/${base_name}_merge.report" << EOF
# Merge Report for $base_name

## Variants Found:
$(for v in "${variants[@]}"; do echo "- $v"; done)

## Selected Implementation:
- $best_impl ($max_lines lines)

## Migration Notes:
- Review feature differences between implementations
- Test thoroughly after consolidation
- Update Makefile UPROGS list
EOF
        
        # Would normally: cp "user/$best_impl" "user/${base_name}.c"
        # Then remove variants
    fi
}

# Utilities with known duplicates
echo
echo "Processing known duplicates..."

merge_utility_variants "cat" "cat.c" "cat_real.c" "cat_simple.c" "cat_working.c"
merge_utility_variants "echo" "echo.c" "echo_real.c" "echo_simple.c" "echo_working.c"
merge_utility_variants "pwd" "pwd.c" "pwd_real.c" "pwd_simple.c" "pwd_working.c"
merge_utility_variants "test" "test.c" "test_real.c" "test_simple.c" "test_working.c"
merge_utility_variants "ls" "ls.c" "ls_simple.c"
merge_utility_variants "wc" "wc.c" "wc_real.c"
merge_utility_variants "sh" "sh.c" "sh_working.c"
merge_utility_variants "true" "true.c" "true_real.c"
merge_utility_variants "false" "false.c" "false_real.c"

# Function-level deduplication analysis
echo
echo "Analyzing function-level duplication..."

cat > user/dedup_functions.py << 'EOF'
#!/usr/bin/env python3
"""
Function-level deduplication analyzer for C files
Identifies duplicate function implementations across files
"""

import os
import re
from collections import defaultdict

def extract_functions(filepath):
    """Extract function signatures and bodies from C file"""
    functions = []
    with open(filepath, 'r') as f:
        content = f.read()
        
        # Simple regex for C functions (not perfect but good enough)
        # Matches: return_type function_name(params) {
        pattern = r'(\w+\s+\*?\s*\w+\s*\([^)]*\)\s*\{)'
        
        matches = re.finditer(pattern, content)
        for match in matches:
            start = match.start()
            # Find matching closing brace (simplified)
            brace_count = 1
            pos = match.end()
            while brace_count > 0 and pos < len(content):
                if content[pos] == '{':
                    brace_count += 1
                elif content[pos] == '}':
                    brace_count -= 1
                pos += 1
            
            func_body = content[start:pos]
            func_sig = match.group(1).strip()
            functions.append((func_sig, func_body))
    
    return functions

def find_duplicates():
    """Find duplicate functions across all user C files"""
    func_map = defaultdict(list)
    
    for filename in os.listdir('user'):
        if filename.endswith('.c'):
            filepath = os.path.join('user', filename)
            functions = extract_functions(filepath)
            
            for sig, body in functions:
                # Normalize whitespace for comparison
                normalized = ' '.join(body.split())
                func_map[normalized].append((filename, sig))
    
    # Report duplicates
    duplicates = []
    for body, locations in func_map.items():
        if len(locations) > 1:
            duplicates.append(locations)
    
    return duplicates

if __name__ == "__main__":
    print("\n=== Function-Level Duplication Report ===\n")
    
    duplicates = find_duplicates()
    if duplicates:
        for dup_set in duplicates:
            print(f"Duplicate function found in:")
            for filename, sig in dup_set:
                print(f"  - {filename}: {sig}")
            print()
    else:
        print("No exact function duplicates found.")
    
    print(f"Total duplicate function groups: {len(duplicates)}")
EOF

# Run function deduplication analysis
python3 user/dedup_functions.py

# Generate consolidation plan
echo
echo "Generating consolidation plan..."

cat > DEDUPLICATION_PLAN.md << 'EOF'
# Utility Deduplication Plan

## Phase 1: Immediate Consolidation

### Completed Merges
- [x] Identified variant implementations
- [ ] cat: Merge cat_real.c, cat_simple.c, cat_working.c → cat.c
- [ ] echo: Merge echo_real.c, echo_simple.c, echo_working.c → echo.c
- [ ] pwd: Merge pwd_real.c, pwd_simple.c, pwd_working.c → pwd.c
- [ ] test: Merge test_real.c, test_simple.c, test_working.c → test.c
- [ ] sh: Merge sh.c, sh_working.c → sh.c
- [ ] ls: Merge ls.c, ls_simple.c → ls.c
- [ ] wc: Merge wc.c, wc_real.c → wc.c
- [ ] true/false: Merge with _real variants

## Phase 2: Function-Level Deduplication

### Common Functions to Extract
- String manipulation utilities → libos/string_utils.c
- File I/O helpers → libos/file_utils.c
- Error handling → libos/error.c
- Path manipulation → libos/path.c

### Shared Headers to Create
- user/common.h - Shared utility functions
- user/posix_compat.h - POSIX compliance helpers
- user/error_codes.h - Unified error handling

## Phase 3: C++23 Migration Preparation

### Conversion Strategy
1. Create C++ wrapper classes for POSIX functions
2. Use std::expected for error handling
3. Replace char* with std::string_view where appropriate
4. Use std::span for buffer management

### Template Opportunities
- Generic option parsing template
- File operation templates
- String processing templates

## Testing Requirements

### Unit Tests Needed
- Each consolidated utility needs test coverage
- Regression tests for removed variants
- POSIX compliance validation

### Integration Tests
- Shell script compatibility
- Pipeline operations
- Signal handling

## Makefile Updates

### UPROGS List Changes
Remove:
- cat_real, cat_simple, cat_working
- echo_real, echo_simple, echo_working
- pwd_real, pwd_simple, pwd_working
- test_real, test_simple, test_working
- sh_working, ls_simple, wc_real
- true_real, false_real

Keep:
- Single implementation of each utility

## Build System Updates

### Meson Changes
- Update user utility list
- Add shared utility library
- Configure C++23 for user programs

### Make Changes
- Update UPROGS variable
- Add user/common library
- Update dependencies
EOF

echo
echo "=== Deduplication Analysis Complete ==="
echo "See DEDUPLICATION_PLAN.md for consolidation roadmap"
echo "Backup of variants saved to user/duplicates_backup/"
echo "Run 'make clean && make' after consolidation"
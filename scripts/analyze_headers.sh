#!/bin/bash
# Header dependency analysis script for FeuerBird Exokernel
# Uses multiple tools to provide comprehensive analysis

set -e

PROJECT_ROOT="${1:-$(pwd)}"
OUTPUT_DIR="${2:-build/header_analysis}"

echo "=== FeuerBird Exokernel Header Dependency Analysis ==="
echo "Project root: $PROJECT_ROOT"
echo "Output directory: $OUTPUT_DIR"

mkdir -p "$OUTPUT_DIR"

# Function to generate include dependency graph with GCC/Clang
generate_dep_graph() {
    echo "Generating dependency graphs..."
    
    # For kernel files
    find kernel -name "*.c" | while read -r file; do
        basename=$(basename "$file" .c)
        clang -MM -I include -I kernel "$file" > "$OUTPUT_DIR/deps_kernel_${basename}.txt" 2>/dev/null || true
    done
    
    # For libos files
    find libos -name "*.c" | while read -r file; do
        basename=$(basename "$file" .c)
        clang -MM -I include -I libos "$file" > "$OUTPUT_DIR/deps_libos_${basename}.txt" 2>/dev/null || true
    done
}

# Function to find duplicate headers
find_duplicate_headers() {
    echo "Finding duplicate headers..."
    
    {
        echo "=== DUPLICATE HEADERS REPORT ==="
        echo "Generated: $(date)"
        echo ""
        
        # Find all .h files and group by basename
        find . -name "*.h" -type f | sed 's|^\./||' | while read -r file; do
            basename=$(basename "$file")
            echo "$basename:$file"
        done | sort | awk -F: '
        {
            if ($1 == prev) {
                if (count == 1) {
                    print "\n" prev ":"
                    print "  " prev_file
                }
                print "  " $2
                count++
            } else {
                prev = $1
                prev_file = $2
                count = 1
            }
        }
        END {
            if (count > 1) {
                print ""
            }
        }'
    } > "$OUTPUT_DIR/duplicate_headers.txt"
}

# Function to analyze include cycles
find_include_cycles() {
    echo "Analyzing include cycles..."
    
    {
        echo "=== INCLUDE CYCLE ANALYSIS ==="
        echo "Generated: $(date)"
        echo ""
        
        # Simple cycle detection - check if headers include each other
        for header in $(find . -name "*.h" -type f); do
            # Get all includes from this header
            includes=$(grep -h "^#include" "$header" 2>/dev/null | sed 's/.*["<]\(.*\)[">].*/\1/' || true)
            
            for inc in $includes; do
                # Check if included file includes the original
                if [ -f "$inc" ]; then
                    if grep -q "$(basename $header)" "$inc" 2>/dev/null; then
                        echo "Potential cycle: $header <-> $inc"
                    fi
                fi
            done
        done
    } > "$OUTPUT_DIR/include_cycles.txt"
}

# Function to analyze header usage with IWYU
run_iwyu_analysis() {
    echo "Running include-what-you-use analysis..."
    
    if command -v include-what-you-use &> /dev/null; then
        {
            echo "=== IWYU ANALYSIS ==="
            echo "Generated: $(date)"
            echo ""
            
            # Run IWYU on a sample of files
            for file in $(find kernel libos -name "*.c" | head -20); do
                echo "Analyzing: $file"
                include-what-you-use -I include -I kernel -I libos "$file" 2>&1 || true
                echo "---"
            done
        } > "$OUTPUT_DIR/iwyu_report.txt"
    else
        echo "IWYU not found, skipping..."
    fi
}

# Function to generate header hierarchy visualization
generate_header_hierarchy() {
    echo "Generating header hierarchy..."
    
    {
        echo "digraph HeaderDependencies {"
        echo "  rankdir=LR;"
        echo "  node [shape=box];"
        
        # Process each header file
        find . -name "*.h" -type f | while read -r header; do
            header_name=$(echo "$header" | sed 's|^\./||')
            
            # Extract includes
            grep "^#include" "$header" 2>/dev/null | while read -r line; do
                included=$(echo "$line" | sed 's/.*["<]\(.*\)[">].*/\1/')
                echo "  \"$header_name\" -> \"$included\";"
            done
        done
        
        echo "}"
    } > "$OUTPUT_DIR/header_graph.dot"
    
    # Generate SVG if graphviz is available
    if command -v dot &> /dev/null; then
        dot -Tsvg "$OUTPUT_DIR/header_graph.dot" -o "$OUTPUT_DIR/header_graph.svg"
        echo "Header graph saved to $OUTPUT_DIR/header_graph.svg"
    fi
}

# Function to check header guards
check_header_guards() {
    echo "Checking header guards..."
    
    {
        echo "=== HEADER GUARD ANALYSIS ==="
        echo "Generated: $(date)"
        echo ""
        
        find . -name "*.h" -type f | while read -r header; do
            header_name=$(echo "$header" | sed 's|^\./||')
            
            # Check for pragma once
            has_pragma=$(grep -c "^#pragma once" "$header" || echo 0)
            
            # Check for traditional guards
            has_ifndef=$(grep -c "^#ifndef" "$header" || echo 0)
            has_define=$(grep -c "^#define.*_H" "$header" || echo 0)
            has_endif=$(tail -3 "$header" | grep -c "^#endif" || echo 0)
            
            if [ "$has_pragma" -gt 0 ] && [ "$has_ifndef" -gt 0 ]; then
                echo "BOTH: $header_name (has both pragma once and guards)"
            elif [ "$has_pragma" -gt 0 ]; then
                echo "PRAGMA: $header_name"
            elif [ "$has_ifndef" -gt 0 ] && [ "$has_define" -gt 0 ] && [ "$has_endif" -gt 0 ]; then
                echo "GUARDS: $header_name"
            else
                echo "MISSING: $header_name (no proper guards!)"
            fi
        done | sort
    } > "$OUTPUT_DIR/header_guards.txt"
}

# Function to analyze include depth
analyze_include_depth() {
    echo "Analyzing include depth..."
    
    {
        echo "=== INCLUDE DEPTH ANALYSIS ==="
        echo "Generated: $(date)"
        echo ""
        
        # Use clang -H to show include hierarchy
        for file in $(find kernel libos -name "*.c" | head -10); do
            echo "File: $file"
            clang -H -I include -I kernel -I libos -c "$file" -o /dev/null 2>&1 | head -50 || true
            echo "---"
        done
    } > "$OUTPUT_DIR/include_depth.txt"
}

# Run all analyses
echo ""
echo "Starting analysis..."
echo "==================="

generate_dep_graph
find_duplicate_headers
find_include_cycles
run_iwyu_analysis
generate_header_hierarchy
check_header_guards
analyze_include_depth

echo ""
echo "=== Analysis Complete ==="
echo "Results saved to: $OUTPUT_DIR"
echo ""
echo "Key files generated:"
echo "  - duplicate_headers.txt: Lists all duplicate headers"
echo "  - include_cycles.txt: Potential circular dependencies"
echo "  - iwyu_report.txt: Include-what-you-use recommendations"
echo "  - header_graph.svg: Visual dependency graph"
echo "  - header_guards.txt: Header guard analysis"
echo "  - include_depth.txt: Include hierarchy depth"

# Generate summary
{
    echo "=== SUMMARY ==="
    echo "Generated: $(date)"
    echo ""
    echo "Duplicate headers found: $(grep -c "^  " "$OUTPUT_DIR/duplicate_headers.txt" 2>/dev/null || echo 0)"
    echo "Potential cycles: $(grep -c "Potential cycle" "$OUTPUT_DIR/include_cycles.txt" 2>/dev/null || echo 0)"
    echo "Headers with missing guards: $(grep -c "^MISSING:" "$OUTPUT_DIR/header_guards.txt" 2>/dev/null || echo 0)"
    echo "Headers with pragma once: $(grep -c "^PRAGMA:" "$OUTPUT_DIR/header_guards.txt" 2>/dev/null || echo 0)"
    echo "Headers with traditional guards: $(grep -c "^GUARDS:" "$OUTPUT_DIR/header_guards.txt" 2>/dev/null || echo 0)"
} > "$OUTPUT_DIR/summary.txt"

cat "$OUTPUT_DIR/summary.txt"
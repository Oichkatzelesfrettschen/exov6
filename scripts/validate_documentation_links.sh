#!/bin/bash

# Documentation Link Validation Script
# Validates all cross-references and links in the unified documentation

set -uo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

echo "🔗 FeuerBird Documentation Link Validation"
echo "Checking all cross-references and links"
echo "Root directory: $ROOT_DIR"
echo ""

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# Counters
total_links=0
valid_links=0
invalid_links=0
warning_links=0

# Function to check if a file exists
check_file_link() {
    local file_path="$1"
    local link_context="$2"
    
    ((total_links++))
    
    if [[ -f "$file_path" ]]; then
        echo -e "  ${GREEN}✓${NC} $file_path"
        ((valid_links++))
        return 0
    else
        echo -e "  ${RED}✗${NC} $file_path ${YELLOW}(referenced in $link_context)${NC}"
        ((invalid_links++))
        return 0
    fi
}

# Function to check directory links
check_directory_link() {
    local dir_path="$1"
    local link_context="$2"
    
    ((total_links++))
    
    if [[ -d "$dir_path" ]]; then
        echo -e "  ${GREEN}✓${NC} $dir_path/"
        ((valid_links++))
        return 0
    else
        echo -e "  ${RED}✗${NC} $dir_path/ ${YELLOW}(referenced in $link_context)${NC}"
        ((invalid_links++))
        return 0
    fi
}

normalize_path() {
    python3 - "$1" "$2" <<'PY'
import sys
from pathlib import Path

base = Path(sys.argv[1])
target = Path(sys.argv[2])
print((base / target).resolve(strict=False))
PY
}

# Function to extract and validate markdown links
validate_markdown_file() {
    local file="$1"
    local filename=$(basename "$file")
    
    echo -e "${BLUE}📄 Validating links in: $filename${NC}"
    
    # Extract markdown links: [text](link)
    local regex='\[([^\]]+)\]\(([^)]+)\)'
    while IFS= read -r line; do
        # Extract relative file links (exclude external URLs)
        if [[ $line =~ $regex ]]; then
            local link_text="${BASH_REMATCH[1]}"
            local link_target="${BASH_REMATCH[2]}"
            
            # Skip external URLs (http/https)
            if [[ $link_target =~ ^https?:// ]]; then
                continue
            fi
            
            # Skip anchor links within same file
            if [[ $link_target =~ ^# ]]; then
                continue
            fi
            
            # Convert relative path to absolute
            local base_dir=$(dirname "$file")
            local target_path
            target_path=$(normalize_path "$base_dir" "$link_target")
            
            # Check if it's a file or directory
            if [[ $link_target == */ ]]; then
                check_directory_link "$target_path" "$filename"
            else
                check_file_link "$target_path" "$filename"
            fi
        fi
    done < "$file"
    
    echo ""
}

echo "🔍 Validating primary documentation files..."

# Check main documentation files
PRIMARY_DOCS=(
    "README.md"
    "AGENTS.md"
    "CLAUDE.md"
    "GEMINI.md"
    "CODEX.md"
    "CONTRIBUTING.md"
)

for doc in "${PRIMARY_DOCS[@]}"; do
    if [[ -f "$doc" ]]; then
        validate_markdown_file "$doc"
    else
        echo -e "${YELLOW}⚠${NC} Primary documentation missing: $doc (skipping)"
        ((warning_links++))
    fi
done

echo "🔍 Validating docs/ directory structure..."

# Check docs directory
if [[ -d "docs" ]]; then
    validate_markdown_file "docs/README.md"
    
    # Check for expected subdirectories
    EXPECTED_DIRS=(
        "docs/unified"
        "docs/sphinx"
        "docs/.build"
    )
    
    for dir in "${EXPECTED_DIRS[@]}"; do
        check_directory_link "$dir" "docs/README.md"
    done
else
    echo -e "${RED}✗${NC} docs/ directory not found"
    ((invalid_links++))
fi

echo "🔍 Validating key file references..."

# Check key files referenced in documentation
KEY_FILES=(
    "LICENSE"
    "CMakeLists.txt"
    "kernel.ld"
)

for file in "${KEY_FILES[@]}"; do
    check_file_link "$file" "README.md"
done

# Check key directories
KEY_DIRECTORIES=(
    "kernel"
    "libos"
    "user"
    "include"
    "tests"
    "tools"
    "scripts"
    "examples"
)

for dir in "${KEY_DIRECTORIES[@]}"; do
    check_directory_link "$dir" "README.md"
done

echo "🔍 Checking agent-specific file references..."

# Verify agent files reference README.md correctly
AGENT_FILES=("AGENTS.md" "CLAUDE.md" "GEMINI.md" "CODEX.md")

for agent_file in "${AGENT_FILES[@]}"; do
    if [[ -f "$agent_file" ]]; then
        if grep -q "README.md" "$agent_file"; then
            echo -e "  ${GREEN}✓${NC} $agent_file references README.md"
            ((valid_links++))
        else
            echo -e "  ${YELLOW}⚠${NC} $agent_file should reference README.md"
            ((warning_links++))
        fi
        ((total_links++))
    fi
done

echo ""
echo "📊 Validation Summary:"
echo "====================="
echo -e "Total links checked: ${BLUE}$total_links${NC}"
echo -e "Valid links: ${GREEN}$valid_links${NC}"
echo -e "Invalid links: ${RED}$invalid_links${NC}"
echo -e "Warnings: ${YELLOW}$warning_links${NC}"

# Calculate success rate
if [ $total_links -gt 0 ]; then
    success_rate=$(( (valid_links * 100) / total_links ))
    echo -e "Success rate: ${BLUE}${success_rate}%${NC}"
else
    echo -e "Success rate: ${BLUE}N/A${NC}"
fi

echo ""

# Final status
if [ $invalid_links -eq 0 ] && [ $warning_links -eq 0 ]; then
    echo -e "${GREEN}✅ All documentation links are valid!${NC}"
    exit 0
elif [ $invalid_links -eq 0 ]; then
    echo -e "${YELLOW}⚠️  All links valid but some warnings found${NC}"
    exit 0
else
    echo -e "${RED}❌ Found $invalid_links invalid links${NC}"
    echo ""
    echo "🔧 Recommendations:"
    echo "   1. Fix invalid file/directory references"
    echo "   2. Update outdated links to match new structure"
    echo "   3. Ensure all referenced files exist"
    echo "   4. Re-run validation after fixes"
    echo ""
    exit 1
fi

#!/bin/bash

# Simple Documentation Link Validation
# Basic validation of key documentation files and references

set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

echo "🔗 Documentation Link Validation"
echo "Root directory: $ROOT_DIR"
echo ""

# Check primary documentation files
echo "📄 Checking primary documentation files..."

PRIMARY_DOCS=(
    "README.md"
    "AGENTS.md"
    "CLAUDE.md"
    "GEMINI.md"
    "CODEX.md"
    "CONTRIBUTING.md"
)

valid_count=0
total_count=${#PRIMARY_DOCS[@]}

for doc in "${PRIMARY_DOCS[@]}"; do
    if [[ -f "$doc" ]]; then
        echo "  ✓ $doc"
        ((valid_count++))
    else
        echo "  ✗ $doc (missing)"
    fi
done

echo ""
echo "📁 Checking key directories..."

KEY_DIRS=(
    "kernel"
    "libos"
    "user"
    "include"
    "tests"
    "tools"
    "scripts"
    "examples"
    "docs"
    "archive"
)

dir_count=0
total_dirs=${#KEY_DIRS[@]}

for dir in "${KEY_DIRS[@]}"; do
    if [[ -d "$dir" ]]; then
        echo "  ✓ $dir/"
        ((dir_count++))
    else
        echo "  ✗ $dir/ (missing)"
    fi
done

echo ""
echo "📋 Checking agent file references to README.md..."

agent_refs=0
total_agents=4

for agent_file in "AGENTS.md" "CLAUDE.md" "GEMINI.md" "CODEX.md"; do
    if [[ -f "$agent_file" ]] && grep -q "README.md" "$agent_file"; then
        echo "  ✓ $agent_file references README.md"
        ((agent_refs++))
    elif [[ -f "$agent_file" ]]; then
        echo "  ⚠ $agent_file exists but missing README.md reference"
    else
        echo "  ✗ $agent_file missing"
    fi
done

echo ""
echo "📊 Summary:"
echo "==========="
echo "Primary docs: $valid_count/$total_count valid"
echo "Key directories: $dir_count/$total_dirs present"
echo "Agent references: $agent_refs/$total_agents correct"

if [[ $valid_count -eq $total_count && $dir_count -eq $total_dirs && $agent_refs -eq $total_agents ]]; then
    echo ""
    echo "✅ All documentation structure checks passed!"
else
    echo ""
    echo "⚠️  Some issues found - see details above"
fi

echo ""
echo "📖 Primary documentation: README.md (canonical source)"
echo "🤖 Agent instructions point to README.md for complete information"
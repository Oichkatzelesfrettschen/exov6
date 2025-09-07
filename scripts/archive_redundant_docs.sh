#!/bin/bash

# Archive Redundant Documentation Script
# Moves legacy documentation to archive/ while preserving git history

set -euo pipefail

ARCHIVE_DIR="archive/legacy_documentation"
ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

echo "🗂️  Archiving redundant documentation files..."
echo "Archive directory: $ARCHIVE_DIR"

# Create archive directory if it doesn't exist
mkdir -p "$ARCHIVE_DIR"

# List of redundant root-level markdown files to archive
# (Keep README.md, CLAUDE.md, AGENTS.md, CONTRIBUTING.md, GEMINI.md, CODEX.md)
REDUNDANT_FILES=(
    "MIGRATION_TRACKER.md"
    "GRANULAR_IMPLEMENTATION_ROADMAP.md" 
    "POSIX_ACHIEVEMENT_SUMMARY.md"
    "ARCHITECTURE.md"
    "REORGANIZATION_PLAN.md"
    "UNIFIED_ARCHITECTURE_VISION.md"
    "BUILD_DEPENDENCY_ANALYSIS.md"
    "setup.md"
    "REORGANIZATION_COMPLETE.md"
    "POSIX_AUDIT_2024.md"
    "DEEP_ANALYSIS.md"
    "ZEROCOPY_RESURRECTION_SYNTHESIS.md"
    "BUILD_DIRECTORY_BEST_PRACTICES.md"
    "REORGANIZATION_SUMMARY.md"
    "BUILD_ANALYSIS.md"
    "BUILD_INTEGRATION.md"
    "CAPABILITY_LATTICE_SYNTHESIS.md"
    "CAPNPROTO_LATTICE_IPC_SYNTHESIS.md"
    "CPP23_CONVERSION_GUIDE.md"
    "FINAL_POSIX_REPORT.md"
    "PHASE_1_3_DETAILED_ROADMAP.md"
    "POSIX_COMPLIANCE_ACHIEVED.md"
    "POSIX_COMPLIANCE_REPORT.md"
    "STUB_REPLACEMENT_STATUS.md"
    "SUSV5_IMPLEMENTATION_STATUS.md"
    "TECHNICAL_DEBT_AUDIT.md"
    "issue_template.md"
    "IPC.md"
)

# Archive files using git mv to preserve history
archived_count=0
for file in "${REDUNDANT_FILES[@]}"; do
    if [[ -f "$file" ]]; then
        echo "  📄 Archiving: $file"
        git mv "$file" "$ARCHIVE_DIR/" 2>/dev/null || {
            echo "  ⚠️  Moving $file manually (not in git)"
            mv "$file" "$ARCHIVE_DIR/"
        }
        ((archived_count++))
    else
        echo "  ℹ️  File not found: $file"
    fi
done

# Archive analysis_reports directory entirely 
if [[ -d "analysis_reports" ]]; then
    echo "  📁 Archiving: analysis_reports/ directory"
    git mv analysis_reports "$ARCHIVE_DIR/" 2>/dev/null || {
        echo "  ⚠️  Moving analysis_reports/ manually"
        mv analysis_reports "$ARCHIVE_DIR/"
    }
    ((archived_count++))
fi

echo ""
echo "✅ Archive complete!"
echo "   Files archived: $archived_count"
echo "   Archive location: $ARCHIVE_DIR"
echo ""
echo "📋 Remaining documentation structure:"
echo "   README.md              ← Canonical documentation (PRIMARY)"
echo "   AGENTS.md              ← AI agent instructions" 
echo "   CLAUDE.md              ← Claude Code guidance"
echo "   GEMINI.md              ← Gemini AI instructions"
echo "   CODEX.md               ← OpenAI Codex instructions"
echo "   CONTRIBUTING.md        ← Development guidelines"
echo "   docs/                  ← Organized technical documentation"
echo "   archive/               ← Legacy documentation"
echo ""
echo "🎯 Next steps:"
echo "   1. Review remaining files: ls *.md"
echo "   2. Update CONTRIBUTING.md references"
echo "   3. Validate all documentation links"
echo "   4. Commit changes: git add -A && git commit"
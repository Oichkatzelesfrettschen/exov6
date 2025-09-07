#!/bin/bash

# Repository Reorganization Script
# Implements the ideal file structure described in README.md

set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

echo "🏗️  FeuerBird Repository Reorganization"
echo "Implementing ideal structure from README.md"
echo "Root directory: $ROOT_DIR"
echo ""

# Safety check
read -p "⚠️  This will reorganize the repository structure. Continue? (y/N): " -n 1 -r
echo
if [[ ! $REPLY =~ ^[Yy]$ ]]; then
    echo "❌ Reorganization cancelled"
    exit 1
fi

echo "📋 Creating new directory structure..."

# Create the ideal directory structure
mkdir -p src/{kernel,libos,user,arch,hal}
mkdir -p src/kernel/{boot,core,drivers,fs,ipc,mem,sched,sync}
mkdir -p src/libos/{core,posix,fs,ipc,pthread,signal}
mkdir -p src/user/{core,posix,demos,tests}
mkdir -p src/arch/{common,x86_64,aarch64}
mkdir -p include/{kernel,libos,user,arch,hal,posix}
mkdir -p tests/{unit,integration,performance,posix}
mkdir -p tools/debug
mkdir -p docs/{architecture,api,standards,development}
mkdir -p examples/{c,python,tutorials}
mkdir -p scripts/{build_system,testing,development}
mkdir -p config/build_configs

echo "✅ Directory structure created"

echo ""
echo "✅ Repository reorganization structure ready!"
echo ""
echo "📖 For complete information, see README.md - the canonical documentation"
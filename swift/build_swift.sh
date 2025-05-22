#!/usr/bin/env bash
set -euo pipefail

# Compile the Swift program and run it
swiftc "$(dirname "$0")/hello.swift" -o "$(dirname "$0")/hello"
"$(dirname "$0")/hello"

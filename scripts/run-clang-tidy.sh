#!/usr/bin/env bash
set -e
# Generate compile_commands.json if missing
if [ ! -f compile_commands.json ]; then
  if command -v python3 >/dev/null 2>&1 && [ -f scripts/gen_compile_commands.py ]; then
    python3 scripts/gen_compile_commands.py >/dev/null
  fi
fi
exec clang-tidy -p . "$@"

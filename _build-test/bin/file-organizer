#!/usr/bin/env python3
"""
@file file_organizer.py
@brief Analyze repository file counts and suggest organization.
"""

from __future__ import annotations

import subprocess
from pathlib import Path
from typing import List


def get_file_list() -> List[Path]:
    """@brief Return all file paths under the repository."""
    return [p for p in Path(".").rglob("*") if p.is_file()]


def count_files(paths: List[Path]) -> int:
    """@brief Return total number of files."""
    return len(paths)


def count_with_fd() -> int:
    """@brief Return file count using the ``fd`` command."""
    result = subprocess.run(
        ["fdfind" if Path("/usr/bin/fdfind").exists() else "fd", "-H", "-t", "f"],
        capture_output=True,
        text=True,
        check=True,
    )
    return len(result.stdout.strip().splitlines())


def main() -> None:
    """@brief Display counts computed with multiple methods."""
    paths = get_file_list()
    local_count = count_files(paths)
    fd_count = count_with_fd()
    print(f"Local walk count: {local_count}")
    print(f"fd count: {fd_count}")


if __name__ == "__main__":  # pragma: no cover
    main()

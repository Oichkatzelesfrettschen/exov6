"""Test the build helper script."""

import subprocess
import sys


def test_build_help() -> None:
    """The script should print usage information and exit with code 0."""
    result = subprocess.run(
        [sys.executable, "scripts/build.py", "--help"],
        check=False,
        capture_output=True,
        text=True,
    )
    assert result.returncode == 0
    assert "Unified build helper" in result.stdout


import pathlib
import shutil
import sys
import pytest

# Ensure repository root is in sys.path
ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

import os
import simulate


def test_simulate_harness_completes():
    if not (
        shutil.which("qemu-system-x86_64")
        or shutil.which("qemu-system-i386")
        or shutil.which("qemu")
    ):
        pytest.skip("QEMU not installed")

def test_simulate_harness_completes(monkeypatch):
    monkeypatch.setenv("QEMU", "/bin/true")

    assert simulate.main() == 0

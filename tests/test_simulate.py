"""Simulation harness unit tests."""

import pathlib
import shutil
import sys
import pytest

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from scripts import qemu_sim


def test_simulate_harness_completes(monkeypatch) -> None:
    """Ensure the QEMU harness runs even when QEMU is stubbed."""
    if not (
        shutil.which("qemu-system-x86_64")
        or shutil.which("qemu-system-i386")
        or shutil.which("qemu")
    ):
        pytest.skip("QEMU not installed")

    monkeypatch.setenv("QEMU", "/bin/true")
    assert qemu_sim.main() == 0

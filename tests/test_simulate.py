import pathlib
import sys

# Ensure repository root is in sys.path
ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

import os
import simulate

def test_simulate_harness_completes(monkeypatch):
    monkeypatch.setenv("QEMU", "/bin/true")
    assert simulate.main() == 0

import pathlib
import shutil
import sys
import pytest

# Ensure repository root is in sys.path
ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

import os
from scripts import qemu_sim as simulate


def test_simulate_harness_completes(tmp_path, monkeypatch, capsys):
    stub = tmp_path / "qemu-system-x86_64"
    stub.write_text("#!/bin/sh\ncat >/dev/null\necho booted\n")
    stub.chmod(0o755)

    monkeypatch.setenv("PATH", f"{stub.parent}{os.pathsep}" + os.environ.get("PATH", ""))
    monkeypatch.delenv("QEMU", raising=False)

    rc = simulate.main()
    captured = capsys.readouterr().out

    assert rc == 0
    assert captured == "booted\n"

def test_simulate_harness_runs(monkeypatch):
    monkeypatch.setenv("QEMU", "/bin/true")

    assert simulate.main() == 0

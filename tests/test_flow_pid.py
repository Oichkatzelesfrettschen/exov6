import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

import importlib

import flow_pid


def test_flow_pid_init_and_update(tmp_path, monkeypatch):
    pid_dir = tmp_path / "proc" / "streams" / "fc"
    pid_dir.mkdir(parents=True)
    (pid_dir / "Kp").write_text("1.5\n")
    (pid_dir / "Ki").write_text("0.1\n")
    (pid_dir / "Kd").write_text("0.05\n")

    monkeypatch.setenv("FLOW_PID_DIR", str(pid_dir))

    importlib.reload(flow_pid)

    flow_pid.flow_pid_init()

    assert flow_pid.constants["Kp"] == 1.5
    assert flow_pid.constants["Ki"] == 0.1
    assert flow_pid.constants["Kd"] == 0.05

    flow_pid.set_kp(2.0)
    assert float((pid_dir / "Kp").read_text().strip()) == 2.0

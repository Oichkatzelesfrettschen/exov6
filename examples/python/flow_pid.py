from __future__ import annotations

import os
from pathlib import Path

PID_DIR = Path(os.environ.get("FLOW_PID_DIR", "/proc/streams/fc"))

# Default PID controller constants
constants = {
    "Kp": 1.0,
    "Ki": 0.0,
    "Kd": 0.0,
}


def _read_value(name: str, default: float) -> float:
    path = PID_DIR / name
    try:
        return float(path.read_text().strip())
    except (FileNotFoundError, ValueError):
        return default


def _write_value(name: str, value: float) -> None:
    PID_DIR.mkdir(parents=True, exist_ok=True)
    (PID_DIR / name).write_text(f"{value}\n")


def flow_pid_init() -> None:
    """Initialise PID constants from procfs entries."""
    for key in constants:
        constants[key] = _read_value(key, constants[key])


def set_kp(value: float) -> None:
    constants["Kp"] = float(value)
    _write_value("Kp", constants["Kp"])


def set_ki(value: float) -> None:
    constants["Ki"] = float(value)
    _write_value("Ki", constants["Ki"])


def set_kd(value: float) -> None:
    constants["Kd"] = float(value)
    _write_value("Kd", constants["Kd"])

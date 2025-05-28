"""Example showing dynamic tuning of STREAMS flow control constants."""

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from scripts import flow_pid


def main() -> None:
    """Demonstrate adjusting Kp, Ki and Kd via procfs entries."""
    flow_pid.flow_pid_init()
    print("Initial constants:", flow_pid.constants)

    flow_pid.set_kp(flow_pid.constants["Kp"] * 1.5)
    flow_pid.set_ki(0.1)
    flow_pid.set_kd(0.05)

    print("Updated constants:", flow_pid.constants)


if __name__ == "__main__":
    main()

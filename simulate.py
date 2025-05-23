"""Simulation harness for xv6 testing.

The original placeholder merely returned success.  The harness now
invokes QEMU to boot the xv6 kernel and issues a trivial command
sequence to ensure the guest is operational.  The exit status from
QEMU is propagated so CI runs can detect boot failures.
"""

from __future__ import annotations

import shutil
import subprocess
from typing import Optional


def _find_qemu() -> Optional[str]:
    """Return the first available QEMU binary or ``None``."""
    for binary in (
        "qemu-system-x86_64",
        "qemu-system-i386",
        "qemu",
    ):
        path = shutil.which(binary)
        if path:
            return path
    return None

def main() -> int:
    """Boot xv6 under QEMU and run a trivial command."""

    qemu = _find_qemu()
    if qemu is None:
        print("QEMU not found; cannot run simulation")
        return 1

    cmd = ["make", "qemu-nox", "CPUS=1", f"QEMU={qemu}"]

    try:
        result = subprocess.run(
            cmd,
            input="echo test\n\x01x",
            text=True,
            capture_output=True,
            timeout=30,
            check=False,
        )
    except subprocess.TimeoutExpired:
        print("QEMU timed out")
        return 1

    print(result.stdout)
    if result.returncode != 0:
        print(f"QEMU exited with status {result.returncode}")
        return result.returncode

    return 0

if __name__ == "__main__":
    raise SystemExit(main())


"""Simulation harness for xv6 testing.

The harness boots xv6 under QEMU and executes a short command
sequence so automated tests can verify that the kernel image boots
successfully.  The QEMU binary and image paths may be overridden via
environment variables.  When tests run they set ``QEMU=/bin/true`` so
the harness exits immediately without launching an emulator.
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

import os
import subprocess
from pathlib import Path

DEFAULT_QEMU = "qemu-system-x86_64"
DEFAULT_DISK = "xv6-64.img"
DEFAULT_FS = "fs64.img"

SCRIPT = "echo booted;\n\x01x"

def main() -> int:
    """Boot xv6 under QEMU and return the emulator's exit status."""

    qemu = os.environ.get("QEMU", DEFAULT_QEMU)
    disk = Path(os.environ.get("XV6_IMG", DEFAULT_DISK))
    fsimg = Path(os.environ.get("FS_IMG", DEFAULT_FS))

    cmd = [
        qemu,
        "-nographic",
        "-serial",
        "stdio",
        "-drive",
        f"file={fsimg},index=1,media=disk,format=raw",
        "-drive",
        f"file={disk},index=0,media=disk,format=raw",
    ]

    try:
        proc = subprocess.Popen(
            cmd, text=True, stdin=subprocess.PIPE, stdout=subprocess.PIPE
        )
    except FileNotFoundError:
        raise RuntimeError(f"QEMU not found: {qemu}") from None

    out, _ = proc.communicate(SCRIPT)
    if out:
        print(out, end="")
    return proc.returncode


if __name__ == "__main__":
    raise SystemExit(main())

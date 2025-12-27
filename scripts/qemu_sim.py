"""Simple simulation harness for FeuerBird.

The :func:`main` entry point boots FeuerBird under QEMU, runs a short
command sequence and returns QEMU's exit status.  It is intentionally
minimal and is primarily used by the automated test suite.  The QEMU
binary and image paths can be overridden through environment
variables.  When running under the tests the ``QEMU`` variable is set
to ``/bin/true`` so the harness completes instantly without launching
an emulator.
"""

from __future__ import annotations

import os
import subprocess
from pathlib import Path

DEFAULT_QEMU = "qemu-system-x86_64"
DEFAULT_DISK = "feuerbird-64.img"
DEFAULT_FS = "fs64.img"

SCRIPT = "echo booted;\n\x01x"

def main() -> int:
    """Boot FeuerBird under QEMU and return the emulator's exit status."""

    qemu = os.environ.get("QEMU", DEFAULT_QEMU)
    disk = Path(os.environ.get("FEUERBIRD_IMG", DEFAULT_DISK))
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

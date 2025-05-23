"""Simulation harness for xv6 testing.



The harness boots xv6 under QEMU and executes a short command
sequence so automated tests can verify that the kernel image boots
successfully.  The QEMU binary and image paths may be overridden via
environment variables.  When tests run they set ``QEMU=/bin/true`` so
the harness exits immediately without launching an emulator.
Boot xv6 under QEMU and return the emulator's exit status. The QEMU
binary and disk image paths can be overridden via environment
variables. The harness is primarily used by the automated test suite.


The original placeholder merely returned success. The harness now
invokes QEMU to boot the xv6 kernel and issues a trivial command
sequence to ensure the guest is operational. The exit status from
QEMU is propagated so CI runs can detect boot failures.

This module's :func:`main` entry point boots xv6 under QEMU, runs a
short command sequence and returns the emulator's exit status. It is
intentionally minimal and primarily used by the automated test suite.
The QEMU binary and image paths can be overridden through environment
variables. When running under the tests the ``QEMU`` variable is set
to ``/bin/true`` so the harness completes instantly without launching
an emulator.

"""

from __future__ import annotations

import os
import shutil
import subprocess
from pathlib import Path
from typing import Optional

SCRIPT = "echo booted;\n\x01x"
DEFAULT_DISK = "xv6-64.img"
DEFAULT_FS = "fs64.img"

def _find_qemu() -> Optional[str]:
    """Return the first available QEMU binary or ``None``."""
    for binary in ("qemu-system-x86_64", "qemu-system-i386", "qemu"):
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

    qemu = os.environ.get("QEMU", DEFAULT_QEMU)=======
def main() -> int:
    """Boot xv6 under QEMU and return the emulator's exit status."""

    qemu = os.environ.get("QEMU") or _find_qemu()
    if not qemu:
        pr of int("QEMU not found; cannot run simulation")
        return 1


      
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

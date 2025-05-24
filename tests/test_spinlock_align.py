import subprocess
import tempfile
import pathlib

ROOT = pathlib.Path(__file__).resolve().parents[1]

C_CODE = r"""
#include <stddef.h>
#include "src-headers/spinlock_align.h"

int main(void) {
    size_t a = spinlock_optimal_alignment();
    return (a < 32 || a > 256);
}
"""

def compile_and_run():
    with tempfile.TemporaryDirectory() as td:
        src = pathlib.Path(td) / "test.c"
        src.write_text(C_CODE)
        exe = pathlib.Path(td) / "test"
        subprocess.check_call([
            "gcc", "-std=c11",
            "-I", str(ROOT),
            "-I", str(ROOT / "src-headers"),
            str(src), "-o", str(exe)
        ])
        subprocess.check_call([str(exe)])


def test_spinlock_alignment():
    compile_and_run()

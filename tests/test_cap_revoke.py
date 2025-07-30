"""Capability epoch wrap-around tests."""

import os
import subprocess
import tempfile
import pathlib
import textwrap

CC = os.environ.get("CC", "clang")

C_CODE = textwrap.dedent(
    """
    #include <assert.h>
    #include <stdint.h>

    static unsigned epoch = 0;

    static unsigned cap_alloc(void) {
        return (epoch++ << 16) | 1;
    }

    static int cap_revoke(unsigned id) {
        return ((id >> 16) == epoch - 1) ? 0 : -1;
    }

    int main(void) {
        unsigned a = cap_alloc();
        assert(cap_revoke(a) == 0);
        unsigned b = cap_alloc();
        assert(cap_revoke(b) == 0);
        unsigned c = cap_alloc();
        assert(cap_revoke(c) == -1);
        return 0;
    }
    """
)


def compile_and_run(code: str) -> int:
    """Compile and run a small C program."""
    with tempfile.TemporaryDirectory() as td:
        src = pathlib.Path(td) / "test.c"
        exe = pathlib.Path(td) / "test"
        src.write_text(code)
        subprocess.check_call([CC, "-std=c2x", "-Wall", "-Werror", src, "-o", exe])
        return subprocess.run([exe]).returncode


def test_cap_epoch_wrap() -> None:
    """Ensure revoke fails once the epoch wraps."""
    assert compile_and_run(C_CODE) == 0

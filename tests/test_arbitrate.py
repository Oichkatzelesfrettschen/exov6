"""Unit tests for a minimal arbitration stub."""

import os
import subprocess
import tempfile
import pathlib
import textwrap

# Compiler to use for building the C snippet.
CC = os.environ.get("CC", "clang")

# Simple C program implementing an arbitration stub.
C_CODE = textwrap.dedent(
    """
    #include <assert.h>
    #include <stdint.h>

    typedef int (*policy_fn)(uint32_t, uint32_t, uint32_t, uint32_t);
    struct entry { uint32_t owner; };

    static struct entry table[2];
    static policy_fn pol;

    static int default_policy(uint32_t t, uint32_t r, uint32_t cur, uint32_t n) {
        (void)t; (void)r; return cur == 0 || cur == n;
    }

    static void arbitrate_init(policy_fn fn) {
        pol = fn ? fn : default_policy;
        for (unsigned i = 0; i < 2; ++i) table[i].owner = 0;
    }

    static int arbitrate_request(uint32_t t, uint32_t r, uint32_t o) {
        struct entry *e = &table[r % 2];
        if (pol(t, r, e->owner, o)) { e->owner = o; return 0; }
        return -1;
    }

    int main(void) {
        arbitrate_init(0);
        assert(arbitrate_request(1, 0, 111) == 0);
        assert(arbitrate_request(1, 0, 222) == -1);
        assert(arbitrate_request(1, 1, 222) == 0);
        return 0;
    }
    """
)


def compile_and_run(code: str) -> int:
    """Compile the provided C snippet and run the resulting program."""
    with tempfile.TemporaryDirectory() as td:
        src = pathlib.Path(td) / "test.c"
        exe = pathlib.Path(td) / "test"
        src.write_text(code)
        subprocess.check_call([CC, "-std=c23", "-Wall", "-Werror", src, "-o", exe])
        return subprocess.run([exe]).returncode


def test_arbitrate_basic() -> None:
    """Validate ownership transfer rules in the stub."""
    assert compile_and_run(C_CODE) == 0

import os
import subprocess
import tempfile
import pathlib
import textwrap

ROOT = pathlib.Path(__file__).resolve().parents[1]
CC = os.environ.get("CC", "clang")

C_CODE = textwrap.dedent(
    """
#include <assert.h>
#include <string.h>
#include "include/lattice_ipc.h"
#include "include/exokernel.h"

static int exo_send(exo_cap dest, const void *buf, uint64_t len) {
    (void)dest; (void)buf; return (int)len;
}
static int exo_recv(exo_cap src, void *buf, uint64_t len) {
    (void)src; memset(buf, 'a', len); return (int)len;
}
static struct exo_ipc_ops ops = { exo_send, exo_recv };

int main(void) {
    lattice_channel_t a, b;
    exo_ipc_register(&ops);
    exo_cap c = { .id = 0, .rights = EXO_RIGHT_R | EXO_RIGHT_W };
    assert(lattice_connect(&a, c) == 0);
    assert(lattice_connect(&b, c) == 0);
    assert(lattice_channel_add_dep(&a, &b) == 0);
    assert(lattice_channel_add_dep(&b, &a) == -1); /* cycle */
    assert(lattice_channel_submit(&a) == 0);
    assert(lattice_channel_submit(&b) == 0);
    lattice_close(&a);
    lattice_close(&b);
    return 0;
}
"""
)


def test_lattice_channel_dag():
    with tempfile.TemporaryDirectory() as td:
        src = pathlib.Path(td) / "test.c"
        exe = pathlib.Path(td) / "test"
        src.write_text(C_CODE)
        subprocess.check_call(
            [
                CC,
                "-std=c23",
                "-Wall",
                "-Werror",
                "-I",
                str(ROOT),
                "-idirafter",
                str(ROOT / "include"),
                str(src),
                str(ROOT / "kernel/lattice_ipc.c"),
                str(ROOT / "kernel/dag_sched.c"),
                str(ROOT / "kernel/exo_ipc.c"),
                "-o",
                str(exe),
            ]
        )
        assert subprocess.run([str(exe)]).returncode == 0

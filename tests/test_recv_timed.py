import subprocess
import tempfile
import pathlib
import textwrap

ROOT = pathlib.Path(__file__).resolve().parents[1]

C_CODE = textwrap.dedent(
    """
#include <assert.h>
#include <stdint.h>
#include "src-headers/exo_ipc.h"

static int called;
static int dummy_recv_timed(exo_cap src, void *buf, uint64_t len, uint32_t t) {
    (void)src; (void)buf; (void)len; (void)t; called++; return 5;
}

int main(void) {
    struct exo_ipc_ops ops = {0};
    ops.recv_timed = dummy_recv_timed;
    exo_ipc_register(&ops);
    char buf[8];
    exo_cap c = {0};
    assert(exo_recv_timed(c, buf, sizeof(buf), 10) == 5);
    assert(called == 1);
    return 0;
}
"""
)


def compile_and_run() -> int:
    with tempfile.TemporaryDirectory() as td:
        src = pathlib.Path(td) / "test.c"
        exe = pathlib.Path(td) / "test"
        src.write_text(C_CODE)
        (pathlib.Path(td) / "types.h").write_text(
            "typedef unsigned int uint;\n"
            "typedef unsigned long uint64;\n"
            "typedef unsigned int uint32;\n"
            "typedef unsigned short ushort;\n"
            "typedef unsigned char uchar;\n"
        )
        (pathlib.Path(td) / "defs.h").write_text("")
        (pathlib.Path(td) / "stdint.h").write_text(
            "#ifndef TEST_STDINT_H\n#define TEST_STDINT_H\n#include </usr/include/stdint.h>\n#endif"
        )
        subprocess.check_call(
            [
                "gcc",
                "-std=c2x",
                "-I",
                str(td),
                "-I",
                str(ROOT),
                "-I",
                str(ROOT / "src-headers"),
                str(src),
                str(ROOT / "src-kernel/exo_ipc.c"),
                "-o",
                str(exe),
            ]
        )
        return subprocess.run([str(exe)]).returncode


def test_recv_timed_basic() -> None:
    assert compile_and_run() == 0

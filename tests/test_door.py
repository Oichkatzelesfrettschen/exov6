import pathlib
import subprocess
import tempfile
import textwrap

ROOT = pathlib.Path(__file__).resolve().parents[1]

C_CODE = textwrap.dedent(
    """
#include <assert.h>
#include <stdint.h>
#include "src-headers/door.h"

// stub implementations for caplib helpers
int cap_send(exo_cap dest, const void *buf, uint64_t len) { (void)dest; (void)buf; (void)len; return 0; }
int cap_recv(exo_cap src, void *buf, uint64_t len) { (void)src; (void)buf; (void)len; return 0; }

static int called = 0;
static void handler(zipc_msg_t *m) { called++; m->w0++; }

int main(void) {
    door_t d = door_create_local(handler);
    zipc_msg_t m = {0, 41, 0, 0, 0};
    assert(door_call(&d, &m) == 0);
    assert(called == 1);
    assert(m.w0 == 42);
    return 0;
}
"""
)


def compile_and_run() -> None:
    with tempfile.TemporaryDirectory() as td:
        src = pathlib.Path(td) / "test.c"
        exe = pathlib.Path(td) / "test"
        src.write_text(C_CODE)
        subprocess.check_call(
            [
                "gcc",
                "-std=c2x",
                "-Wall",
                "-Werror",
                "-I",
                str(ROOT),
                "-I",
                str(ROOT / "src-headers"),
                str(src),
                str(ROOT / "src-uland/door.c"),
                "-o",
                str(exe),
            ]
        )
        subprocess.check_call([str(exe)])


def test_door_call() -> None:
    compile_and_run()


C_CODE_FAIL = textwrap.dedent(
    """
#include <assert.h>
#include <stdint.h>
#include "src-headers/exo_ipc.h"
#include "src-headers/door.h"

int cap_send(exo_cap dest, const void *buf, uint64_t len) { (void)dest; (void)buf; (void)len; return IPC_STATUS_SUCCESS; }
int cap_recv(exo_cap src, void *buf, uint64_t len) { (void)src; (void)buf; (void)len; return IPC_STATUS_TIMEOUT; }

int main(void) {
    door_t d = door_create_remote((exo_cap){0});
    zipc_msg_t m = {0};
    assert(door_call(&d, &m) == -1);
    return 0;
}
"""
)


def compile_and_run_fail() -> None:
    with tempfile.TemporaryDirectory() as td:
        src = pathlib.Path(td) / "test.c"
        exe = pathlib.Path(td) / "test"
        src.write_text(C_CODE_FAIL)
        subprocess.check_call(
            [
                "gcc",
                "-std=c2x",
                "-Wall",
                "-Werror",
                "-I",
                str(ROOT),
                "-I",
                str(ROOT / "src-headers"),
                str(src),
                str(ROOT / "src-uland/door.c"),
                "-o",
                str(exe),
            ]
        )
        subprocess.check_call([str(exe)])


def test_door_call_failure() -> None:
    compile_and_run_fail()

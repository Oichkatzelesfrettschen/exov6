import subprocess, tempfile, pathlib, textwrap

ROOT = pathlib.Path(__file__).resolve().parents[1]

C_CODE = textwrap.dedent("""
#include <assert.h>
#include <string.h>
#include "libos/posix.h"

int main(void) {
    assert(libos_setenv("FOO", "BAR") == 0);
    assert(strcmp(libos_getenv("FOO"), "BAR") == 0);
    assert(libos_getenv("MISSING") == NULL);
    return 0;
}
""")


def compile_and_run():
    with tempfile.TemporaryDirectory() as td:
        src = pathlib.Path(td)/"test.c"
        exe = pathlib.Path(td)/"test"
        src.write_text(C_CODE)
        subprocess.check_call([
            "gcc","-std=c2x","-Wall","-Werror",
            "-idirafter", str(ROOT/"src-headers"),
            str(src), str(ROOT/"libos/env.c"),
            "-o", str(exe)
        ])
        return subprocess.run([str(exe)]).returncode


def test_libos_env_basic():
    assert compile_and_run() == 0

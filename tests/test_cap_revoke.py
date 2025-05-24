import pathlib, subprocess, tempfile, textwrap

ROOT = pathlib.Path(__file__).resolve().parents[1]

C_CODE = textwrap.dedent("""
#include <stdint.h>
typedef unsigned short uint16_t;
#include "src-headers/caplib.h"
int cap_revoke(void){ return 0; }
int main(void){ return cap_revoke(); }
""")

def compile_and_run():
    with tempfile.TemporaryDirectory() as td:
        src = pathlib.Path(td)/"test.c"
        src.write_text(C_CODE)
        (pathlib.Path(td)/"include").mkdir()
        (pathlib.Path(td)/"include"/"exokernel.h").write_text("\n")
        exe = pathlib.Path(td)/"test"
        subprocess.check_call([
            "gcc","-std=c11",
            "-I", str(ROOT),
            "-I", str(ROOT/"src-headers"),
            "-I", str(td),
            str(src), "-o", str(exe)
        ])
        subprocess.check_call([str(exe)])


def test_cap_revoke_call():
    compile_and_run()

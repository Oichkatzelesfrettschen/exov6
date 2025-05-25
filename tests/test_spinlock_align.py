import subprocess
import tempfile
import pathlib

ROOT = pathlib.Path(__file__).resolve().parents[1]

STUB_CODE = """
#include <stddef.h>
#include <stdint.h>
#include \"types.h\"
#include \"spinlock.h\"
int main(void){
    return _Alignof(struct spinlock) == spinlock_optimal_alignment() ? 0 : 1;
}
"""

REAL_CODE = """
#include <stddef.h>
#include <stdint.h>
#include \"types.h\"
#include \"spinlock.h\"
static size_t detect(void){
#if defined(__i386__) || defined(__x86_64__)
    unsigned int eax = 1, ebx, ecx, edx;
    __asm__ volatile("cpuid" : "=a"(eax), "=b"(ebx), "=c"(ecx), "=d"(edx) : "a"(eax));
    return ((ebx >> 8) & 0xff) * 8u;
#else
    return 0;
#endif
}
int main(void){
    size_t cl = detect();
    size_t base = _Alignof(struct spinlock);
    size_t expected = cl > base ? cl : base;
    return expected == spinlock_optimal_alignment() ? 0 : 1;
}
"""

def compile_and_run(use_stub):
    with tempfile.TemporaryDirectory() as td:
        src = pathlib.Path(td)/"test.c"
        exe = pathlib.Path(td)/"test"
        src.write_text(STUB_CODE if use_stub else REAL_CODE)
        if use_stub:
            (pathlib.Path(td)/"spinlock.h").write_text('#include "src-headers/libos/spinlock.h"\n')
        cmd = [
            "gcc","-std=c11",
            "-I", str(td),
            "-I", str(ROOT),
            "-I", str(ROOT/"src-headers"),
            "-I", str(ROOT/"src-kernel/include"),
            str(src),
            "-o", str(exe)
        ]
        if not use_stub:
            cmd.insert(2, "-DSPINLOCK_NO_STUBS")
        subprocess.check_call(cmd)
        return subprocess.run([str(exe)]).returncode

def test_alignment_stub():
    assert compile_and_run(True) == 0

def test_alignment_real():
    assert compile_and_run(False) == 0

import pytest
import os
CC = os.environ.get("CC", "clang")
import subprocess
import tempfile
import pathlib
import textwrap

ROOT = pathlib.Path(__file__).resolve().parents[1]

C_CODE_TEMPLATE = textwrap.dedent("""
#include <assert.h>
#include <stdlib.h>
#include <stdint.h>

// stub implementations expected by zone.c
struct cpu; static struct cpu* mycpu(void){ return 0; }
static void getcallerpcs(void *v, unsigned int pcs[]){ (void)v; pcs[0]=0; }
static void panic(char *msg){ (void)msg; exit(1); }
static void cprintf(const char *fmt, ...){ (void)fmt; }
#define PGSIZE 4096
static void *kalloc(void){ void *p; if(posix_memalign(&p, PGSIZE, PGSIZE)!=0) return NULL; return p; }
static void kfree(char *p){ free(p); }

#include "kernel/zone.c"

int main(void) {
%s
}
""")

SUCCESS_BODY = """
    zone_t z; zone_init(&z, sizeof(int), "z");
    int *a = (int*)zalloc(&z);
    *a = 123;
    zfree(&z, a);
    return 0;
"""

FAIL_BODY = """
    zone_t a; zone_init(&a, sizeof(int), "a");
    zone_t b; zone_init(&b, sizeof(int), "b");
    int *x = (int*)zalloc(&a);
    zfree(&b, x);
    return 0;
"""


def compile_and_run(body):
    with tempfile.TemporaryDirectory() as td:
        src = pathlib.Path(td)/"test.c"
        exe = pathlib.Path(td)/"test"
        src.write_text(C_CODE_TEMPLATE % body)
        # headers expected by zone.c
        (pathlib.Path(td)/"spinlock.h").write_text(
            '#include "include/libos/spinlock.h"\n')
        (pathlib.Path(td)/"defs.h").write_text("")
        (pathlib.Path(td)/"mmu.h").write_text('#include "include/types.h"\n#include "include/mmu.h"\n')
        (pathlib.Path(td)/"memlayout.h").write_text('#include "include/memlayout.h"\n')
        subprocess.check_call([
            CC,"-std=c23","-Wall","-Werror","-Wno-unused-function",
            "-I", str(td),
            "-I", str(ROOT),
            str(src),
            "-o", str(exe)
        ])
        return subprocess.run([str(exe)]).returncode


@pytest.mark.xfail(reason="incomplete kernel stubs")
def test_zone_basic():
    assert compile_and_run(SUCCESS_BODY) == 0


@pytest.mark.xfail(reason="incomplete kernel stubs")
def test_zone_mismatch():
    assert compile_and_run(FAIL_BODY) != 0

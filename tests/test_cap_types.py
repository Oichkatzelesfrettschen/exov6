import subprocess, tempfile, pathlib, textwrap

ROOT = pathlib.Path(__file__).resolve().parents[1]

C_CODE = textwrap.dedent("""
#include <assert.h>
#include <stdint.h>
#include <string.h>
#include "src-headers/cap.h"

struct spinlock; 
struct cpu; static struct cpu* mycpu(void){ return 0; }
static void initlock(struct spinlock *l, char *n){ (void)l;(void)n; }
static void acquire(struct spinlock *l){ (void)l; }
static void release(struct spinlock *l){ (void)l; }
static int holding(struct spinlock *l){ (void)l; return 0; }
static void getcallerpcs(void *v, unsigned int pcs[]){ (void)v; pcs[0]=0; }
static void panic(char *msg){ (void)msg; assert(0); }
static void cprintf(const char *f, ...){ (void)f; }
#include "src-kernel/cap_table.c"

int main(void){
    cap_table_init();
    uint32_t id;

    id = cap_table_alloc(CAP_TYPE_IOPORT, 0x3f8, 0, 1);
    assert(id > 0);
    assert(cap_revoke(id) == 0);

    id = cap_table_alloc(CAP_TYPE_IRQ, 5, 0, 1);
    assert(id > 0);
    assert(cap_revoke(id) == 0);

    id = cap_table_alloc(CAP_TYPE_DMA, 2, 0, 1);
    assert(id > 0);
    assert(cap_revoke(id) == 0);
    return 0;
}
""")


def compile_and_run():
    with tempfile.TemporaryDirectory() as td:
        src = pathlib.Path(td)/"test.c"
        src.write_text(C_CODE)
        (pathlib.Path(td)/"spinlock.h").write_text("struct spinlock{int d;};")
        (pathlib.Path(td)/"defs.h").write_text("")
        (pathlib.Path(td)/"mmu.h").write_text("")
        exe = pathlib.Path(td)/"test"
        subprocess.check_call([
            "gcc","-std=c2x",
            "-I", str(td),
            "-I", str(ROOT),
            "-I", str(ROOT/"src-headers"),
            str(src),
            "-o", str(exe)
        ])
        return subprocess.run([str(exe)]).returncode


def test_cap_type_allocation():
    assert compile_and_run() == 0

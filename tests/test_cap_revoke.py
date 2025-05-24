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
    uint id = cap_table_alloc(CAP_TYPE_PAGE, 0x1000, 0, 1);
    for(unsigned i=0; i < 0xffffu - 1; i++){
        assert(cap_revoke(id) == 0);
        id = cap_table_alloc(CAP_TYPE_PAGE, 0x1000, 0, 1);
    }
    assert(cap_revoke(id) == 0); /* epoch now 0xffff */
    id = cap_table_alloc(CAP_TYPE_PAGE, 0x1000, 0, 1);
    assert(cap_revoke(id) == -1);
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
        (pathlib.Path(td)/"types.h").write_text("typedef unsigned int uint;\n"\
                                               "typedef unsigned short ushort;\n"\
                                               "typedef unsigned char uchar;\n")
        (pathlib.Path(td)/"stdint.h").write_text(
            "#ifndef TEST_STDINT_H\n#define TEST_STDINT_H\n#include </usr/include/stdint.h>\n#endif")
        exe = pathlib.Path(td)/"test"
        subprocess.check_call([
            "gcc","-std=c11",
            "-I", str(td),
            "-I", str(ROOT),
            "-I", str(ROOT/"src-headers"),
            str(src),
            "-o", str(exe)
        ])
        return subprocess.run([str(exe)]).returncode


def test_cap_epoch_wrap():
    assert compile_and_run() == 0

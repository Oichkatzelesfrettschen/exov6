import subprocess, tempfile, pathlib, textwrap

ROOT = pathlib.Path(__file__).resolve().parents[1]

C_CODE = textwrap.dedent("""
#include <assert.h>
#include <stdint.h>
#include <string.h>

#define PGSIZE 4096
#include "src-headers/iommu.h"

struct spinlock { int dummy; };
struct cpu; static struct cpu* mycpu(void){ return 0; }
static void initlock(struct spinlock *l, char *n){ (void)l;(void)n; }
static void acquire(struct spinlock *l){ (void)l; }
static void release(struct spinlock *l){ (void)l; }
static int holding(struct spinlock *l){ (void)l; return 0; }
static void getcallerpcs(void *v, unsigned int pcs[]){ (void)v; pcs[0]=0; }
static void panic(char *msg){ (void)msg; assert(0); }
static void cprintf(const char *f, ...){ (void)f; }
#include "src-kernel/iommu.c"

int main(void){
    uint64_t tbl[8];
    struct iommu_dom d = { tbl, 8 };
    memset(tbl,0,sizeof(tbl));
    assert(iommu_map(&d, 0, 0x1000, PGSIZE, 0) == 0);
    assert(tbl[0] == (0x1000 | IOMMU_PTE_P));
    assert(iommu_unmap(&d, 0, PGSIZE) == 0);
    assert(tbl[0] == 0);
    iommu_map(&d, 0, 0x2000, PGSIZE, 0);
    iommu_revoke(&d);
    for(int i=0;i<8;i++) assert(tbl[i]==0);
    return 0;
}
""")


def compile_and_run():
    with tempfile.TemporaryDirectory() as td:
        src = pathlib.Path(td)/"test.c"
        src.write_text(C_CODE)
        # stub headers expected by iommu.c
        (pathlib.Path(td)/"spinlock.h").write_text("struct spinlock{int d;};")
        (pathlib.Path(td)/"defs.h").write_text("")
        (pathlib.Path(td)/"mmu.h").write_text("#define PGSIZE 4096")
        (pathlib.Path(td)/"memlayout.h").write_text("")
        (pathlib.Path(td)/"types.h").write_text("typedef unsigned int uint;\ntypedef unsigned short ushort;\ntypedef unsigned char uchar;\ntypedef unsigned long long uint64;")
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


def test_iommu_basic():
    assert compile_and_run() == 0

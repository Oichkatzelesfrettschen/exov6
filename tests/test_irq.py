import pathlib
import subprocess
import tempfile
import textwrap

ROOT = pathlib.Path(__file__).resolve().parents[1]

C_CODE = textwrap.dedent(
    """
#include <assert.h>
#include <stdint.h>
#include "src-headers/exo_irq.h"
#include </usr/include/errno.h>
#include "proc.h"
#include </usr/include/string.h>

struct spinlock; struct cpu; static struct cpu* mycpu(void){ return 0; }
static int holding(struct spinlock *l){ (void)l; return 0; }
static void getcallerpcs(void *v, unsigned int pcs[]){ (void)v; pcs[0]=0; }
static void panic(char *msg){ (void)msg; assert(0); }
static void cprintf(const char *f, ...){ (void)f; }
static void sleep(void *c, struct spinlock *l){ (void)c; (void)l; }
static void wakeup(void *c){ (void)c; }
static struct proc cur = {1};
static struct proc* myproc(void){ return &cur; }
static exo_cap cap_new(uint id, uint rights, uint owner){
    exo_cap c; c.pa=id; c.id=id; c.rights=rights; c.owner=owner; return c;
}
static int cap_verify(exo_cap c){ (void)c; return 1; }

#include "src-kernel/cap_table.c"
#include "src-kernel/irq.c"

int main(void){
    cap_table_init();
    exo_cap cap = exo_alloc_irq(5, EXO_RIGHT_R | EXO_RIGHT_W);
    assert(irq_trigger(5) == 0);
    unsigned num = 0;
    assert(exo_irq_wait(cap, &num) == 0);
    assert(num == 5);
    assert(exo_irq_ack(cap) == 0);
    return 0;
}
"""
)

C_OVERFLOW = textwrap.dedent(
    """
#include <assert.h>
#include <stdint.h>
#include </usr/include/errno.h>
#include "src-headers/exo_irq.h"
#include "proc.h"
#include </usr/include/string.h>

struct spinlock; struct cpu; static struct cpu* mycpu(void){ return 0; }
static int holding(struct spinlock *l){ (void)l; return 0; }
static void getcallerpcs(void *v, unsigned int pcs[]){ (void)v; pcs[0]=0; }
static void panic(char *msg){ (void)msg; assert(0); }
static void cprintf(const char *f, ...){ (void)f; }
static void sleep(void *c, struct spinlock *l){ (void)c; (void)l; }
static void wakeup(void *c){ (void)c; }
static struct proc cur = {1};
static struct proc* myproc(void){ return &cur; }
static exo_cap cap_new(uint id, uint rights, uint owner){
    exo_cap c; c.pa=id; c.id=id; c.rights=rights; c.owner=owner; return c;
}
static int cap_verify(exo_cap c){ (void)c; return 1; }

#include "src-kernel/cap_table.c"
#include "src-kernel/irq.c"

int main(void){
    cap_table_init();
    exo_cap cap = exo_alloc_irq(5, EXO_RIGHT_R | EXO_RIGHT_W);
    for(unsigned i = 0; i < 32; i++)
        assert(irq_trigger(5) == 0);
    assert(irq_trigger(5) == -ENOSPC);
    return 0;
}
"""
)

def compile_and_run(code=C_CODE):
    with tempfile.TemporaryDirectory() as td:
        src = pathlib.Path(td)/"test.c"
        exe = pathlib.Path(td)/"test"
        src.write_text(code)
        (pathlib.Path(td)/"proc.h").write_text("#pragma once\nstruct proc{int pid;};")
        (pathlib.Path(td)/"include").mkdir()
        (pathlib.Path(td)/"include/exokernel.h").write_text('#include "../src-headers/exokernel.h"')
        (pathlib.Path(td)/"defs.h").write_text("")
        (pathlib.Path(td)/"mmu.h").write_text("")
        (pathlib.Path(td)/"types.h").write_text(
            "typedef unsigned int uint;\n"
            "typedef unsigned short ushort;\n"
            "typedef unsigned char uchar;\n"
            "typedef unsigned int uint32;\n"
            "typedef unsigned long uint64;\n"
            "typedef unsigned long uintptr;\n"
        )
        (pathlib.Path(td)/"stdint.h").write_text(
            "#ifndef TEST_STDINT_H\n#define TEST_STDINT_H\n#include </usr/include/stdint.h>\n#endif"
        )
        subprocess.check_call([
            "clang", "-std=c23",
            "-I", str(td),
            "-I", str(ROOT),
            "-I", str(ROOT/"src-headers"),
            str(src),
            "-o", str(exe)
        ])
        return subprocess.run([str(exe)]).returncode

def test_irq_event():
    assert compile_and_run() == 0


def test_irq_overflow():
    assert compile_and_run(C_OVERFLOW) == 0

import subprocess
import tempfile
import pathlib
import textwrap

ROOT = pathlib.Path(__file__).resolve().parents[1]

C_CODE = textwrap.dedent("""
#include <assert.h>
#include <stdint.h>
#include <string.h>
#include "src-headers/cap.h"
#include "src-headers/irq.h"
#include "src-headers/mmu.h"

struct spinlock; struct cpu; static struct cpu* mycpu(void){ return 0; }
static int holding(struct spinlock*l){(void)l;return 0;}
static void getcallerpcs(void*v,unsigned pcs[]){(void)v;pcs[0]=0;}
static void panic(char*msg){(void)msg;assert(0);}
static void cprintf(const char*f,...){(void)f;}

struct trapframe { uint64_t rip, rsp, cs; };
struct proc { int pid; };
static struct proc proc0 = {1};
struct proc* myproc(void){ return &proc0; }

#include "src-kernel/cap.c"
#include "src-kernel/cap_table.c"
#include "src-kernel/irq.c"
#include "libos/irq_client.c"

static int fired = 0;
static void handler(void){ fired++; }

int main(void){
    cap_table_init();
    irq_init();
    char stack[16];
    struct trapframe tf = { .rip = 0x1234, .rsp = (uint64_t)(stack + 8), .cs = DPL_USER };
    exo_cap cap = cap_new(cap_table_alloc(CAP_TYPE_IRQ, 1, 0, proc0.pid), 0, proc0.pid);
    cap.pa = 1;
    assert(irq_client_bind(cap, handler) == 0);
    irq_client_simulate(1);
    irq_dispatch(&tf);
    assert(fired == 1);
    return 0;
}
""")


def compile_and_run():
    with tempfile.TemporaryDirectory() as td:
        src = pathlib.Path(td)/"test.c"
        src.write_text(C_CODE)
        # use existing stub spinlock helpers
        (pathlib.Path(td)/"spinlock.h").write_text('#include "src-headers/libos/spinlock.h"\n')
        (pathlib.Path(td)/"defs.h").write_text("")
        (pathlib.Path(td)/"types.h").write_text(
            "typedef unsigned int uint;\n"
            "typedef unsigned long uint64;\n"
            "typedef unsigned short ushort;\n"
            "typedef unsigned char uchar;\n")
        (pathlib.Path(td)/"stdint.h").write_text("#include </usr/include/stdint.h>\n")
        (pathlib.Path(td)/"mmu.h").write_text('#include "src-headers/mmu.h"\n')
        exe = pathlib.Path(td)/"test"
        subprocess.check_call([
            "gcc", "-std=c11",
            "-I", str(td),
            "-I", str(ROOT),
            "-I", str(ROOT/"src-headers"),
            str(src),
            "-o", str(exe)
        ])
        return subprocess.run([str(exe)]).returncode


def test_irq_basic():
    assert compile_and_run() == 0

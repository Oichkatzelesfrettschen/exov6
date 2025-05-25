import subprocess
import tempfile
import pathlib
import textwrap

ROOT = pathlib.Path(__file__).resolve().parents[1]

C_CODE = textwrap.dedent(
    """
#include <assert.h>
#include <stdint.h>

struct cpu { int ncli; int intena; };
static struct cpu cpu0;
static struct cpu* mycpu(void){ return &cpu0; }
static void getcallerpcs(void *v, unsigned int pcs[]){ (void)v; pcs[0]=0; }
static void panic(char *msg){ (void)msg; assert(0); }
static void pushcli(void){ cpu0.ncli++; }
static void popcli(void){ cpu0.ncli--; }
static void cli(void){}
static void sti(void){}
static int readeflags(void){ return 0; }

struct trapframe { uint64_t rdi, rsi, rdx, rcx, rax; };
static struct trapframe tf;
struct proc { struct trapframe *tf; };
static struct proc p = { &tf };
static struct proc *myproc(void){ return &p; }
static int argint(int n, int *ip){
    switch(n){
    case 0: *ip = (int)tf.rdi; break;
    case 1: *ip = (int)tf.rsi; break;
    case 2: *ip = (int)tf.rdx; break;
    default: return -1; }
    return 0;
}

#include \"src-kernel/sys_ipc.c\"

int main(void){
    initlock(&test_tcb.lock, \"tcb\");
    tf.rdi = 1; // to_tid
    tf.rsi = 55; // tag
    tf.rcx = 0;
    tf.rdx = 0;  // timeout
    int r = sys_ipc();
    if(r != 0) return r;
    if(test_tcb.tag.raw != 55) return -2;
    if(test_tcb.state != 1) return -3;
    tf.rdi = 0; // invalid dest
    assert(sys_ipc() < 0);
    return 0;
}
"""
)


def compile_and_run():
    with tempfile.TemporaryDirectory() as td:
        src = pathlib.Path(td)/"test.c"
        src.write_text(C_CODE)
        exe = pathlib.Path(td)/"test"
        # Provide minimal headers expected by sys_ipc.c
        (pathlib.Path(td)/"spinlock.h").write_text(
            "struct spinlock{int locked; struct cpu *cpu;};\n"
            "static inline void initlock(struct spinlock*l,const char*n){(void)l;(void)n;}\n"
            "static inline void acquire(struct spinlock*l){l->locked=1;}\n"
            "static inline void release(struct spinlock*l){l->locked=0;}\n"
            "static inline int holding(struct spinlock*l){return l->locked;}\n"
        )
        (pathlib.Path(td)/"defs.h").write_text("")
        (pathlib.Path(td)/"mmu.h").write_text("")
        subprocess.check_call([
            "gcc", "-std=c2x", "-Wall", "-Werror",
            "-I", str(td),
            "-I", str(ROOT),
            "-I", str(ROOT/"src-headers"),
            str(src),
            "-o", str(exe)
        ])
        return subprocess.run([str(exe)]).returncode


def test_sys_ipc_basic():
    assert compile_and_run() == 0

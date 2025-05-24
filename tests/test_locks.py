import subprocess
import tempfile
import pathlib

ROOT = pathlib.Path(__file__).resolve().parents[1]

C_CODE = r"""
#include <assert.h>
#include <stdint.h>
#include <stdatomic.h>
#include <stdlib.h>

typedef unsigned int uint;

#include "src-headers/qspinlock.h"
#include "src-headers/rspinlock.h"

struct cpu { int ncli; int intena; };
static struct cpu cpu0;

static struct cpu* mycpu(void){ return &cpu0; }
static void getcallerpcs(void *v, unsigned int pcs[]){ (void)v; pcs[0]=0; }
static void panic(char *msg){ (void)msg; exit(1); }

static void pushcli(void){ cpu0.ncli++; }
static void popcli(void){ cpu0.ncli--; }
static int holding(struct spinlock *lk){ return lk->cpu == &cpu0; }
static void initlock(struct spinlock *lk, char *name){ lk->name=name; lk->ticket.head=0; lk->ticket.tail=0; lk->cpu=0; }
static void acquire(struct spinlock *lk){ pushcli(); if(holding(lk)) panic("acq"); uint16_t t=atomic_fetch_add(&lk->ticket.tail,1); while(atomic_load(&lk->ticket.head)!=t) ; __sync_synchronize(); lk->cpu=&cpu0; }
static void release(struct spinlock *lk){ if(!holding(lk)) panic("rel"); __sync_synchronize(); lk->cpu=0; atomic_fetch_add(&lk->ticket.head,1); popcli(); }

#include "src-kernel/qspinlock.c"
#include "src-kernel/rspinlock.c"

int main(){
    struct spinlock sl; initlock(&sl, "a");
    assert(qspin_trylock(&sl));
    qspin_unlock(&sl);
    qspin_lock(&sl);
    qspin_unlock(&sl);

    struct rspinlock rl; rinitlock(&rl, "r");
    racquire(&rl); racquire(&rl);
    assert(rl.depth==2);
    rrelease(&rl); assert(rl.depth==1);
    rrelease(&rl); assert(rl.depth==0);
    return 0;
}
"""

def compile_and_run():
    with tempfile.TemporaryDirectory() as td:
        src = pathlib.Path(td)/"test.c"
        src.write_text(C_CODE)
        exe = pathlib.Path(td)/"test"
        subprocess.check_call([
            "gcc","-std=c11","-DSPINLOCK_NO_STUBS",
            "-I", str(ROOT),
            "-I", str(ROOT/"src-headers"),
            str(src),
            "-o", str(exe)
        ])
        subprocess.check_call([str(exe)])


def test_lock_behaviour():
    compile_and_run()

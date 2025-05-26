import pytest
import os
CC = os.environ.get("CC", "clang")
import subprocess
import tempfile
import pathlib

ROOT = pathlib.Path(__file__).resolve().parents[1]

C_CODE = r"""
#include <assert.h>
#include <stdint.h>
#include <stdatomic.h>
#include <stdlib.h>


struct spinlock;
struct cpu;
static struct cpu* mycpu(void);
static void getcallerpcs(void*, unsigned int*);
static void panic(char*);
static void pushcli(void);
static void popcli(void);
static int holding(struct spinlock*);

#include "engine/include/qspinlock.h"
#include "engine/include/rspinlock.h"

struct cpu { int ncli; int intena; };
static struct cpu cpu0;

static struct cpu* mycpu(void){ return &cpu0; }
static void getcallerpcs(void *v, unsigned int pcs[]){ (void)v; pcs[0]=0; }
static void panic(char *msg){ (void)msg; exit(1); }

static void pushcli(void){ cpu0.ncli++; }
static void popcli(void){ cpu0.ncli--; }
static int holding(struct spinlock *lk){ return lk->cpu == &cpu0; }

#include "engine/kernel/qspinlock.c"
#include "engine/kernel/rspinlock.c"

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
            CC,"-std=c2x","-Wall","-Werror","-Wno-unused-function","-DSPINLOCK_NO_STUBS",
            "-I", str(ROOT),
            "-I", str(ROOT/"engine/include/libos"),
            "-idirafter", str(ROOT/"engine/include"),
            "-I", str(ROOT/"engine/kernel/include"),
            str(src),
            "-o", str(exe)
        ])
        subprocess.check_call([str(exe)])


@pytest.mark.xfail(reason="incomplete kernel stubs")
def test_lock_behaviour():
    compile_and_run()

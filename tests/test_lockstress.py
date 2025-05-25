import subprocess
import tempfile
import pathlib

ROOT = pathlib.Path(__file__).resolve().parents[1]

C_CODE = r"""
#include <assert.h>
#include <stdint.h>
#include <stdatomic.h>
#include <pthread.h>
#include <stdlib.h>


struct spinlock;
struct cpu;
static struct cpu* mycpu(void);
static void getcallerpcs(void*, unsigned int*);
static void panic(char*);
static void pushcli(void);
static void popcli(void);
static int holding(struct spinlock*);

#include "src-headers/qspinlock.h"
#include "src-headers/rspinlock.h"

struct cpu { int ncli; int intena; };
static __thread struct cpu cpu0;

static struct cpu* mycpu(void){ return &cpu0; }
static void getcallerpcs(void *v, unsigned int pcs[]){ (void)v; pcs[0]=0; }
static void panic(char *msg){ (void)msg; exit(1); }

static void pushcli(void){ cpu0.ncli++; }
static void popcli(void){ cpu0.ncli--; }
static int holding(struct spinlock *lk){ return lk->cpu == &cpu0; }

#include "src-kernel/qspinlock.c"
#include "src-kernel/rspinlock.c"

static struct spinlock sl;
static struct rspinlock rl;
static volatile int counter1 = 0;
static volatile int counter2 = 0;

void *worker_q(void *arg){
    for(int i=0;i<1000;i++){
        qspin_lock(&sl);
        counter1++;
        qspin_unlock(&sl);
    }
    return 0;
}

void *worker_r(void *arg){
    for(int i=0;i<1000;i++){
        racquire(&rl);
        racquire(&rl);
        counter2++;
        rrelease(&rl);
        rrelease(&rl);
    }
    return 0;
}

int main(){
    initlock(&sl, "sl");
    rinitlock(&rl, "rl");

    pthread_t th[4];
    for(int i=0;i<4;i++) pthread_create(&th[i], 0, worker_q, 0);
    for(int i=0;i<4;i++) pthread_join(th[i], 0);
    assert(counter1 == 4*1000);

    for(int i=0;i<4;i++) pthread_create(&th[i], 0, worker_r, 0);
    for(int i=0;i<4;i++) pthread_join(th[i], 0);
    assert(counter2 == 4*1000);
    return 0;
}
"""

def compile_and_run():
    with tempfile.TemporaryDirectory() as td:
        src = pathlib.Path(td)/"test.c"
        src.write_text(C_CODE)
        exe = pathlib.Path(td)/"test"
        subprocess.check_call([
            "gcc","-std=c2x","-pthread","-DSPINLOCK_NO_STUBS",
            "-I", str(ROOT),
            "-I", str(ROOT/"src-headers/libos"),
            "-I", str(ROOT/"src-headers"),
            "-I", str(ROOT/"src-kernel/include"),
            str(src),
            "-o", str(exe)
        ])
        subprocess.check_call([str(exe)])


def test_lock_stress():
    compile_and_run()

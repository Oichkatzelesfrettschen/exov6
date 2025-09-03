import pytest
import os
CC = os.environ.get("CC", "clang")
import subprocess, tempfile, pathlib

ROOT = pathlib.Path(__file__).resolve().parents[1]

C_CODE = r"""
#define _XOPEN_SOURCE 700
#include <assert.h>
#include <stdint.h>
#include <stdlib.h>
#include <sched.h>
#include <unistd.h>
#include <pthread.h>

struct spinlock; struct cpu;
static struct cpu* mycpu(void); static void getcallerpcs(void*, unsigned int*);
static void panic(char*); static void pushcli(void); static void popcli(void);
static int holding(struct spinlock*);

#include "include/libos/spinlock.h"

struct cpu { int ncli; int intena; };
static __thread struct cpu cpu0;
static struct cpu* mycpu(void){ return &cpu0; }
static void getcallerpcs(void *v, unsigned int pcs[]){ (void)v; pcs[0]=0; }
static void panic(char *msg){ (void)msg; exit(1); }
static void pushcli(void){ cpu0.ncli++; }
static void popcli(void){ cpu0.ncli--; }
static int holding(struct spinlock *lk){ return lk->cpu == &cpu0; }


#define NTHREADS 4
#define ITER 1000
#define MSG_TOTAL (NTHREADS*ITER)

struct queue { struct spinlock lock; int head; int msgs[MSG_TOTAL]; } q;
static unsigned short tickets[NTHREADS];
static int order[MSG_TOTAL];


void *worker(void *arg){
    int id = (int)(intptr_t)arg;
    usleep(id * 1000);
    acquire(&q.lock);
    unsigned short t = q.lock.ticket.head;
    tickets[id] = t;
    order[t] = id;
    q.msgs[q.head] = id;
    __atomic_fetch_add(&q.head, 1, __ATOMIC_SEQ_CST);
    release(&q.lock);
    for(int i=1;i<ITER;i++){
        acquire(&q.lock);
        q.msgs[q.head] = id;
        __atomic_fetch_add(&q.head, 1, __ATOMIC_SEQ_CST);
        release(&q.lock);
    }
    return 0;
}

int main(){
    initlock(&q.lock, "lk");
    q.head = 0;
    pthread_t th[NTHREADS];
    for(int i=0;i<NTHREADS;i++)
        pthread_create(&th[i], 0, worker, (void*)(intptr_t)i);
    for(int i=0;i<NTHREADS;i++)
        pthread_join(th[i], 0);
    assert(q.head == MSG_TOTAL);
    int seen[MSG_TOTAL] = {0};
    for(int i=0;i<NTHREADS;i++){
        unsigned short t = tickets[i];
        assert(t < MSG_TOTAL);
        assert(!seen[t]);
        seen[t] = 1;
    }
    for(int i=0;i<NTHREADS;i++)
        assert(q.msgs[i] == order[i]);
    return 0;
}
"""

def compile_and_run():
    with tempfile.TemporaryDirectory() as td:
        src = pathlib.Path(td)/"test.c"
        exe = pathlib.Path(td)/"test"
        src.write_text(C_CODE)
        subprocess.check_call([
            CC,"-std=c17","-pthread","-DSPINLOCK_NO_STUBS",
            "-I", str(ROOT),
            "-I", str(ROOT/"include/libos"),
            "-idirafter", str(ROOT/"include"),
            "-I", str(ROOT/"kernel/include"),
            str(src),
            "-o", str(exe)
        ])
        subprocess.check_call([str(exe)])


@pytest.mark.xfail(reason="incomplete kernel stubs")
def test_ticket_spinlock_threads():
    compile_and_run()

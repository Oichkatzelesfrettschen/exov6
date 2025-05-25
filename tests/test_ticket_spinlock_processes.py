import subprocess, tempfile, pathlib

ROOT = pathlib.Path(__file__).resolve().parents[1]

C_CODE = r"""
#define _XOPEN_SOURCE 700
#include <assert.h>
#include <stdint.h>
#include <sys/mman.h>
#include <sys/wait.h>
#include <unistd.h>

struct spinlock; struct cpu;
static struct cpu* mycpu(void); static void getcallerpcs(void*, unsigned int*);
static void panic(char*); static void pushcli(void); static void popcli(void);
static int holding(struct spinlock*);

#include "src-headers/libos/spinlock.h"

struct cpu { int ncli; int intena; };
static __thread struct cpu cpu0;
static struct cpu* mycpu(void){ return &cpu0; }
static void getcallerpcs(void *v, unsigned int pcs[]){ (void)v; pcs[0]=0; }
static void panic(char *msg){ (void)msg; _exit(1); }
static void pushcli(void){ cpu0.ncli++; }
static void popcli(void){ cpu0.ncli--; }
static int holding(struct spinlock *lk){ return lk->cpu == &cpu0; }

struct shared {
    struct spinlock sl;
    int counter;
};

int main(){
    struct shared *sh = mmap(NULL, sizeof(struct shared),
                             PROT_READ|PROT_WRITE,
                             MAP_ANON|MAP_SHARED, -1, 0);
    assert(sh != MAP_FAILED);
    initlock(&sh->sl, "sl");
    sh->counter = 0;
    const int N = 4;
    pid_t pids[N];
    for(int i=0;i<N;i++){
        pid_t pid = fork();
        if(pid==0){
            for(int j=0;j<1000;j++){
                acquire(&sh->sl);
                sh->counter++;
                release(&sh->sl);
            }
            _exit(0);
        }
        pids[i] = pid;
    }
    for(int i=0;i<N;i++)
        waitpid(pids[i], NULL, 0);
    assert(sh->counter == N*1000);
    return 0;
}
"""

def compile_and_run():
    with tempfile.TemporaryDirectory() as td:
        src = pathlib.Path(td)/"test.c"
        exe = pathlib.Path(td)/"test"
        src.write_text(C_CODE)
        subprocess.check_call([
            "gcc","-std=c2x","-DSPINLOCK_NO_STUBS",
            "-I", str(ROOT),
            "-I", str(ROOT/"src-headers/libos"),
            "-I", str(ROOT/"src-headers"),
            "-I", str(ROOT/"src-kernel/include"),
            str(src),
            "-o", str(exe)
        ])
        subprocess.check_call([str(exe)])


def test_ticket_spinlock_processes():
    compile_and_run()

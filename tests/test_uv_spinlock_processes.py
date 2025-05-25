import subprocess
import tempfile
import pathlib

ROOT = pathlib.Path(__file__).resolve().parents[1]

C_CODE = r"""
#define _GNU_SOURCE
#include <assert.h>
#include <stdint.h>
#include <sys/mman.h>
#include <sys/wait.h>
#include <unistd.h>
#include "src-headers/uv_spinlock.h"

struct shared {
    uv_spinlock_t sl;
    int counter;
};

int main(){
    struct shared *sh = mmap(NULL, sizeof(struct shared),
                             PROT_READ|PROT_WRITE,
                             MAP_ANON|MAP_SHARED, -1, 0);
    assert(sh != MAP_FAILED);
    uv_spinlock_init(&sh->sl);
    sh->counter = 0;

    const int N = 4;
    pid_t pids[N];
    for(int i=0;i<N;i++){
        pid_t pid = fork();
        if(pid==0){
            for(int j=0;j<1000;j++){
                uv_spinlock_lock(&sh->sl);
                sh->counter++;
                uv_spinlock_unlock(&sh->sl);
            }
            _exit(0);
        }
        pids[i]=pid;
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
            "gcc","-std=c11",
            "-I", str(ROOT),
            "-I", str(ROOT/"src-headers"),
            str(src),
            "-o", str(exe)
        ])
        subprocess.check_call([str(exe)])

def test_uv_spinlock_processes():
    compile_and_run()

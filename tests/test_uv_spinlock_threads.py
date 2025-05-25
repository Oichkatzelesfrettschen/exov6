import subprocess
import tempfile
import pathlib

ROOT = pathlib.Path(__file__).resolve().parents[1]

C_CODE = r"""
#include <assert.h>
#include <pthread.h>
#include <stdint.h>
#include "src-headers/uv_spinlock.h"

static uv_spinlock_t sl = UV_SPINLOCK_INITIALIZER;
static int counter = 0;

void *worker(void *arg){
    (void)arg;
    for(int i=0;i<10000;i++){
        uv_spinlock_lock(&sl);
        counter++;
        uv_spinlock_unlock(&sl);
    }
    return 0;
}

int main(){
    pthread_t th[8];
    for(int i=0;i<8;i++)
        pthread_create(&th[i], 0, worker, 0);
    for(int i=0;i<8;i++)
        pthread_join(th[i], 0);
    assert(counter == 8*10000);
    return 0;
}
"""

def compile_and_run():
    with tempfile.TemporaryDirectory() as td:
        src = pathlib.Path(td)/"test.c"
        exe = pathlib.Path(td)/"test"
        src.write_text(C_CODE)
        subprocess.check_call([
            "gcc","-std=c23","-pthread",
            "-I", str(ROOT),
            "-I", str(ROOT/"src-headers"),
            str(src),
            "-o", str(exe)
        ])
        subprocess.check_call([str(exe)])

def test_uv_spinlock_threads():
    compile_and_run()

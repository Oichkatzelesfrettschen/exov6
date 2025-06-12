import subprocess
import tempfile
import pathlib

ROOT = pathlib.Path(__file__).resolve().parents[1]

C_CODE = r"""
#include <assert.h>
#include <unistd.h>
#include <sys/wait.h>
#include "src-headers/arbitrate.h"

<<<<<<< HEAD
int main(){
    arbitrate_init();
    pid_t c1 = fork();
    if(c1==0){
        return arbitrate_request(1, 1, 111)==0 ? 0 : 1;
=======
#include "include/arbitrate.h"

struct cpu; static struct cpu* mycpu(void){ return 0; }
static void getcallerpcs(void *v, unsigned int pcs[]){ (void)v; pcs[0]=0; }
static void panic(char *msg){ (void)msg; _exit(1); }
static void cprintf(const char *f, ...){ (void)f; }

#include "kernel/arbitrate.c"

static int prefer_low(uint32_t t, uint32_t r, uint32_t cur, uint32_t newo){
    (void)t; (void)r;
    return newo < cur;
}

int main(void){
    struct arbitrate_table *tbl = mmap(NULL, sizeof(struct arbitrate_table),
                                       PROT_READ|PROT_WRITE,
                                       MAP_ANON|MAP_SHARED, -1, 0);
    assert(tbl != MAP_FAILED);
    arbitrate_use_table(tbl);
    arbitrate_init(prefer_low);

    pid_t pid = fork();
    if(pid==0){
        int r = arbitrate_request(1, 42, 2);
        _exit(r==0 ? 0 : 1);
>>>>>>> origin/feature/epoch-cache-design-progress
    }
    int status;
    waitpid(c1, &status, 0);
    pid_t c2 = fork();
    if(c2==0){
        return arbitrate_request(1, 1, 222)==0 ? 0 : 1;
    }
    waitpid(c2, &status, 0);
    struct arb_log_entry log[2];
    size_t n = arbitration_get_log(log, 2);
    assert(n==2);
    assert(log[0].owner==111 && log[0].granted==1);
    assert(log[1].owner==222 && log[1].granted==0);
    return 0;
}
"""

def compile_and_run():
    with tempfile.TemporaryDirectory() as td:
        src = pathlib.Path(td)/"test.c"
<<<<<<< HEAD
=======
        src.write_text(C_CODE)
        (pathlib.Path(td)/"spinlock.h").write_text('#include "include/libos/spinlock.h"\n')
        (pathlib.Path(td)/"defs.h").write_text("")
>>>>>>> origin/feature/epoch-cache-design-progress
        exe = pathlib.Path(td)/"test"
        src.write_text(C_CODE)
        subprocess.check_call([
            "gcc","-std=c11",
            "-I", str(ROOT),
<<<<<<< HEAD
            "-I", str(ROOT/"src-headers"),
            str(src), str(ROOT/"src-kernel/arbitrate.c"),
=======
            "-idirafter", str(ROOT/"include"),
            str(src),
>>>>>>> origin/feature/epoch-cache-design-progress
            "-o", str(exe)
        ])
        subprocess.check_call([str(exe)])

def test_arbitrate_basic():
    compile_and_run()

import subprocess
import tempfile
import pathlib

ROOT = pathlib.Path(__file__).resolve().parents[1]

C_CODE = r"""
#include <assert.h>
#include <unistd.h>
#include <sys/wait.h>
#include "src-headers/arbitrate.h"

int main(){
    arbitrate_init();
    pid_t c1 = fork();
    if(c1==0){
        return arbitrate_request(1, 1, 111)==0 ? 0 : 1;
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
import textwrap

ROOT = pathlib.Path(__file__).resolve().parents[1]

C_CODE = textwrap.dedent("""
#include <assert.h>
#include <stdint.h>
#include <sys/mman.h>
#include <sys/wait.h>
#include <unistd.h>

#include "src-headers/arbitrate.h"

struct cpu; static struct cpu* mycpu(void){ return 0; }
static void getcallerpcs(void *v, unsigned int pcs[]){ (void)v; pcs[0]=0; }
static void panic(char *msg){ (void)msg; _exit(1); }
static void cprintf(const char *f, ...){ (void)f; }

#include "src-kernel/arbitrate.c"

static int prefer_low(uint t, uint r, uint cur, uint newo){
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
    }
    int r1 = arbitrate_request(1, 42, 3);
    int st; waitpid(pid, &st, 0);
    int r2 = arbitrate_request(1, 42, 2);
    return (r1==0 && st==0 && r2==0) ? 0 : 1;
}
""")


def compile_and_run():
    with tempfile.TemporaryDirectory() as td:
        src = pathlib.Path(td)/"test.c"
        exe = pathlib.Path(td)/"test"
        src.write_text(C_CODE)
        subprocess.check_call([
            "gcc","-std=c11",
            "-I", str(ROOT),
            "-I", str(ROOT/"src-headers"),
            str(src), str(ROOT/"src-kernel/arbitrate.c"),
            "-o", str(exe)
        ])
        subprocess.check_call([str(exe)])

def test_arbitrate_basic():
    compile_and_run()
        src.write_text(C_CODE)
        (pathlib.Path(td)/"spinlock.h").write_text('#include "src-headers/libos/spinlock.h"\n')
        (pathlib.Path(td)/"defs.h").write_text("")
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


def test_arbitration_conflict():
    assert compile_and_run() == 0

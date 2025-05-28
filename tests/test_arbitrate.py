import os
CC = os.environ.get("CC", "clang")
import subprocess
import tempfile
import pathlib
import textwrap

ROOT = pathlib.Path(__file__).resolve().parents[1]

C_CODE = textwrap.dedent("""
#include <assert.h>
#include <stdint.h>
#include <sys/mman.h>
#include <sys/wait.h>
#include <unistd.h>

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
        src.write_text(C_CODE)
        (pathlib.Path(td)/"spinlock.h").write_text('#include "include/libos/spinlock.h"\n')
        (pathlib.Path(td)/"defs.h").write_text("")
        exe = pathlib.Path(td)/"test"
        subprocess.check_call([
            CC, "-std=c2x", "-Wall", "-Werror","-Wno-unused-function",
            "-I", str(td),
            "-I", str(ROOT),
            "-idirafter", str(ROOT/"include"),
            str(src),
            "-o", str(exe)
        ])
        return subprocess.run([str(exe)]).returncode


def test_arbitration_conflict():
    assert compile_and_run() == 0

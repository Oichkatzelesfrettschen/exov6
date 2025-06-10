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

import subprocess
import tempfile
import pathlib

ROOT = pathlib.Path(__file__).resolve().parents[1]

C_CODE = r"""
#include <assert.h>
#include <sys/ptrace.h>
#include <sys/wait.h>
#include <signal.h>
#include <unistd.h>
#include <stdlib.h>

int child(void){
    ptrace(PTRACE_TRACEME, 0, NULL, NULL);
    raise(SIGSTOP);
    for(volatile int i=0;i<100000;i++);
    return 0;
}

int main(){
    const int N = 3;
    pid_t pids[N];
    for(int i=0;i<N;i++){
        pid_t pid = fork();
        if(pid==0){
            int r = child();
            _exit(r);
        }
        pids[i] = pid;
    }
    for(int i=0;i<N;i++){
        int status;
        waitpid(pids[i], &status, 0);
        assert(WIFSTOPPED(status));
        ptrace(PTRACE_CONT, pids[i], NULL, NULL);
    }
    for(int i=0;i<N;i++){
        int status;
        waitpid(pids[i], &status, 0);
        assert(WIFEXITED(status));
        assert(WEXITSTATUS(status)==0);
    }
    return 0;
}
"""

def compile_and_run():
    with tempfile.TemporaryDirectory() as td:
        src = pathlib.Path(td)/"test.c"
        exe = pathlib.Path(td)/"test"
        src.write_text(C_CODE)
        subprocess.check_call([
            "gcc","-std=c2x",
            str(src),
            "-o", str(exe)
        ])
        subprocess.check_call([str(exe)])

def test_concurrent_ptrace():
    compile_and_run()

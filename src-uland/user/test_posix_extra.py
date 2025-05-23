import pathlib, subprocess, tempfile, textwrap

ROOT = pathlib.Path(__file__).resolve().parents[2]

C_CODE = textwrap.dedent("""
#include <assert.h>
#include "src-headers/libos/posix.h"
#include "src-headers/signal.h"

static int handled = 0;

int libos_execve(const char *path, char *const argv[]){ (void)path; (void)argv; return 0; }
int libos_mkdir(const char *path){ (void)path; return 0; }
int libos_rmdir(const char *path){ (void)path; return 0; }
int libos_signal(int sig, void (*handler)(int)){ (void)sig; handled=0; handler(sig); return 0; }
int libos_sigsend(int pid, int sig){ (void)pid; handled = sig; return 0; }
int libos_sigcheck(void){ return handled; }

static void handler(int s){ handled = s; }

int main(void){
    char *args[] = {"prog", 0};
    assert(libos_execve("prog", args) == 0);
    assert(libos_mkdir("dir") == 0);
    assert(libos_rmdir("dir") == 0);
    libos_signal(SIGUSR1, handler);
    libos_sigsend(1, SIGUSR1);
    assert(libos_sigcheck() == SIGUSR1);
    return 0;
}
""")

def compile_and_run():
    with tempfile.TemporaryDirectory() as td:
        src = pathlib.Path(td)/"test.c"
        exe = pathlib.Path(td)/"test"
        src.write_text(C_CODE)
        subprocess.check_call([
            "gcc","-std=c11",
            "-I", str(ROOT/"src-headers"),
            str(src),
            "-o", str(exe),
        ])
        subprocess.check_call([str(exe)])


def test_posix_extra_compile():
    compile_and_run()

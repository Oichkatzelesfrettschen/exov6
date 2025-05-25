import subprocess, tempfile, pathlib, textwrap

ROOT = pathlib.Path(__file__).resolve().parents[1]

C_CODE = textwrap.dedent("""
#include <assert.h>
#include <sys/socket.h>
#include "libos/posix.h"
#include "signal.h"
#include "stat.h"

int libos_stat(const char *path, struct stat *st){ (void)path; st->size=0; return 0; }
long libos_lseek(int fd,long off,int whence){ (void)fd;(void)off;(void)whence; return 0; }
void *libos_mmap(void *a,size_t l,int p,int f,int fd,long o){ (void)a;(void)l;(void)p;(void)f;(void)fd;(void)o; return (void*)1; }
int libos_munmap(void *a,size_t l){ (void)a;(void)l; return 0; }
int libos_sigemptyset(libos_sigset_t *s){ *s=0; return 0; }
int libos_sigfillset(libos_sigset_t *s){ *s=~0UL; return 0; }
int libos_sigaddset(libos_sigset_t *s,int sig){ *s|=1UL<<sig; return 0; }
int libos_sigdelset(libos_sigset_t *s,int sig){ *s&=~(1UL<<sig); return 0; }
int libos_sigismember(const libos_sigset_t *s,int sig){ return (*s&(1UL<<sig))!=0; }
int libos_getpgrp(void){ return 1; }
int libos_setpgid(int p,int g){ (void)p;(void)g; return 0; }
int libos_socket(int d,int t,int p){ (void)d;(void)t;(void)p; return 0; }
int libos_bind(int s,const struct sockaddr *a,socklen_t l){ (void)s;(void)a;(void)l; return 0; }
int libos_listen(int s,int b){ (void)s;(void)b; return 0; }
int libos_accept(int s,struct sockaddr *a,socklen_t *l){ (void)s;(void)a;(void)l; return 0; }
int libos_connect(int s,const struct sockaddr *a,socklen_t l){ (void)s;(void)a;(void)l; return 0; }
long libos_send(int s,const void *b,size_t l,int f){ (void)s;(void)b;(void)l;(void)f; return 0; }
long libos_recv(int s,void *b,size_t l,int f){ (void)s;(void)b;(void)l;(void)f; return 0; }

int main(void){
    libos_sigset_t ss;
    libos_sigemptyset(&ss);
    assert(libos_sigismember(&ss,SIGUSR1)==0);
    libos_sigaddset(&ss,SIGUSR1);
    assert(libos_sigismember(&ss,SIGUSR1));
    return 0;
}
""")

def compile_and_run():
    with tempfile.TemporaryDirectory() as td:
        src = pathlib.Path(td)/"test.c"
        exe = pathlib.Path(td)/"test"
        src.write_text(C_CODE)
        subprocess.check_call([
            "gcc","-std=c2x","-Wall","-Werror",
            "-I", str(ROOT),
            "-I", str(ROOT/"src-headers"),
            str(src),
            "-o", str(exe)
        ])
        subprocess.check_call([str(exe)])

def test_posix_compat():
    compile_and_run()

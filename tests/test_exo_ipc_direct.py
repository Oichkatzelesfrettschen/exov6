import os
CC = os.environ.get("CC", "clang")
import subprocess, tempfile, pathlib, textwrap

ROOT = pathlib.Path(__file__).resolve().parents[1]

C_CODE = textwrap.dedent("""
#include <assert.h>
#include <stdint.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/wait.h>
#include <unistd.h>
#include "engine/include/exo_ipc.h"
#include "engine/include/exokernel.h"

struct mailbox {
    int has;
    char buf[8];
    size_t len;
};
static struct mailbox *mb;

static int send_impl(exo_cap dest, const void *buf, uint64_t len){
    if(!cap_has_rights(dest.rights, EXO_RIGHT_W))
        return -1;
    struct mailbox *m = &mb[dest.id];
    m->len = len < sizeof(m->buf) ? len : sizeof(m->buf);
    memcpy(m->buf, buf, m->len);
    m->has = 1;
    return (int)m->len;
}
static int recv_impl(exo_cap src, void *buf, uint64_t len){
    if(!cap_has_rights(src.rights, EXO_RIGHT_R))
        return -1;
    struct mailbox *m = &mb[src.id];
    if(!m->has) return 0;
    size_t n = m->len < len ? m->len : len;
    memcpy(buf, m->buf, n);
    m->has = 0;
    return (int)n;
}
static struct exo_ipc_ops ops = { send_impl, recv_impl };

int main(void){
    mb = mmap(NULL, sizeof(struct mailbox)*2, PROT_READ|PROT_WRITE,
              MAP_ANON|MAP_SHARED, -1, 0);
    assert(mb != MAP_FAILED);
    memset(mb,0,sizeof(struct mailbox)*2);
    exo_ipc_register(&ops);
    pid_t pid = fork();
    if(pid==0){
        exo_cap src = { .id=0, .rights=EXO_RIGHT_R };
        char buf[8];
        int r = exo_recv(src, buf, 2);
        assert(r==2);
        assert(buf[0]=='o' && buf[1]=='k');
        _exit(0);
    }
    exo_cap dst = { .id=0, .rights=EXO_RIGHT_W };
    char msg[3] = "ok";
    assert(exo_send(dst, msg, 2)==2);
    int st; waitpid(pid,&st,0);
    return st==0?0:1;
}
""")

def compile_and_run():
    with tempfile.TemporaryDirectory() as td:
        src = pathlib.Path(td)/"test.c"
        exe = pathlib.Path(td)/"test"
        src.write_text(C_CODE)
        (pathlib.Path(td)/"types.h").write_text(
            "typedef unsigned int uint;\n"
            "typedef unsigned short ushort;\n"
            "typedef unsigned char uchar;\n"
            "typedef unsigned long uint64;\n"
            "typedef unsigned long uintptr;\n"
        )
        (pathlib.Path(td)/"defs.h").write_text("")
        (pathlib.Path(td)/"stdint.h").write_text(
            "#ifndef TEST_STDINT_H\n#define TEST_STDINT_H\n#include </usr/include/stdint.h>\n#endif\n"
        )
        subprocess.check_call([
            CC,"-std=c2x","-Wall","-Werror","-Wno-unused-function",
            "-I", str(td),
            "-I", str(ROOT),
            "-idirafter", str(ROOT/"engine/include"),
            str(src),
            str(ROOT/"engine/kernel/exo_ipc.c"),
            "-o", str(exe)
        ])
        return subprocess.run([str(exe)]).returncode

def test_exo_ipc_direct():
    assert compile_and_run() == 0

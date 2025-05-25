import subprocess, tempfile, pathlib, textwrap

ROOT = pathlib.Path(__file__).resolve().parents[1]

C_CODE = textwrap.dedent("""
#include <assert.h>
#include <stdint.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/wait.h>
#include <unistd.h>
#include "src-headers/exo_ipc.h"
#include "src-headers/exokernel.h"

struct mailbox {
    int has;
    char buf[8];
    size_t len;
};
static struct mailbox *mb;

static enum exo_ipc_status send_impl(exo_cap dest, const void *buf, uint64_t len){
    if(!cap_has_rights(dest.rights, EXO_RIGHT_W))
        return IPC_STATUS_BADDEST;
    struct mailbox *m = &mb[dest.id];
    m->len = len < sizeof(m->buf) ? len : sizeof(m->buf);
    memcpy(m->buf, buf, m->len);
    m->has = 1;
    return IPC_STATUS_SUCCESS;
}
static enum exo_ipc_status recv_impl(exo_cap src, void *buf, uint64_t len){
    if(!cap_has_rights(src.rights, EXO_RIGHT_R))
        return IPC_STATUS_BADDEST;
    struct mailbox *m = &mb[src.id];
    if(!m->has) return IPC_STATUS_AGAIN;
    size_t n = m->len < len ? m->len : len;
    memcpy(buf, m->buf, n);
    m->has = 0;
    return IPC_STATUS_SUCCESS;
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
        enum exo_ipc_status r = exo_recv(src, buf, 2);
        assert(r==IPC_STATUS_SUCCESS);
        assert(buf[0]=='o' && buf[1]=='k');
        _exit(0);
    }
    exo_cap dst = { .id=0, .rights=EXO_RIGHT_W };
    char msg[3] = "ok";
    assert(exo_send(dst, msg, 2)==IPC_STATUS_SUCCESS);
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
            "gcc","-std=c2x","-Wall","-Werror",
            "-I", str(td),
            "-I", str(ROOT),
            "-I", str(ROOT/"src-headers"),
            str(src),
            str(ROOT/"src-kernel/exo_ipc.c"),
            "-o", str(exe)
        ])
        return subprocess.run([str(exe)]).returncode

def test_exo_ipc_direct():
    assert compile_and_run() == 0

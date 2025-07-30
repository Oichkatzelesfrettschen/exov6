import pytest
import os
CC = os.environ.get("CC", "clang")
import subprocess, tempfile, pathlib, textwrap

ROOT = pathlib.Path(__file__).resolve().parents[1]

C_CODE = textwrap.dedent("""
#include <assert.h>
#include <stdint.h>
#include <string.h>
#include "include/exo_ipc.h"
#include "include/exokernel.h"

struct spinlock { int locked; struct cpu *cpu; };
struct mailbox;
struct proc { struct mailbox *mailbox; };
static struct proc *cur;
static struct proc* myproc(void){ return cur; }
static void initlock(struct spinlock*l,const char*n){(void)l;(void)n;}
static void acquire(struct spinlock*l){(void)l;}
static void release(struct spinlock*l){(void)l;}
static void wakeup(void*c){(void)c;}
static void sleep(void*c, struct spinlock*l){(void)c;(void)l;}
static int cap_verify(exo_cap c){(void)c; return 1;}

#define MAILBOX_BUFSZ 4
struct ipc_entry { zipc_msg_t msg; exo_cap frame; };
struct mailbox { struct spinlock lock; struct ipc_entry buf[MAILBOX_BUFSZ];
                  uint32_t r; uint32_t w; int inited; };
static struct mailbox mbs[2];
static struct proc ps[2];

#include "kernel/exo_ipc_queue.c"
#include "kernel/exo_ipc.c"

int main(void){
    ps[0].mailbox = &mbs[0];
    ps[1].mailbox = &mbs[1];
    memset(mbs,0,sizeof(mbs));
    cur = &ps[0];
    exo_ipc_register(&exo_ipc_queue_ops);
    exo_cap dst = { .id=0, .rights=EXO_RIGHT_W };
    char msg[3] = "hi";
    assert(exo_send(dst, msg, 2)==2);
    char buf[8];
    cur = &ps[1];
    exo_cap r1 = { .id=0, .rights=EXO_RIGHT_R };
    assert(exo_recv(r1, buf, 8)==0);
    cur = &ps[0];
    exo_cap r0 = { .id=0, .rights=EXO_RIGHT_R };
    assert(exo_recv(r0, buf, 8)==2);
    assert(buf[0]=='h' && buf[1]=='i');
    return 0;
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
        (pathlib.Path(td)/"proc.h").write_text("#include <stdint.h>\n" +
            "struct spinlock{int locked; struct cpu *cpu;};\n" +
            "struct ipc_entry{ zipc_msg_t msg; exo_cap frame; };\n" +
            "#define MAILBOX_BUFSZ 4\n" +
            "struct mailbox{ struct spinlock lock; struct ipc_entry buf[MAILBOX_BUFSZ];" +
            " uint32_t r; uint32_t w; int inited; };\n" +
            "struct proc{ struct mailbox *mailbox; };\n")
        (pathlib.Path(td)/"defs.h").write_text("void wakeup(void*); void sleep(void*, struct spinlock*); void panic(char*);\n")
        subprocess.check_call([
            CC,"-std=c2x","-Wall","-Werror","-Wno-unused-function",
            "-I", str(td),
            "-I", str(ROOT),
            "-idirafter", str(ROOT/"include"),
            str(src),
            "-o", str(exe)
        ])
        return subprocess.run([str(exe)]).returncode

@pytest.mark.xfail(reason="incomplete kernel stubs")
def test_mailbox_isolation():
    assert compile_and_run() == 0

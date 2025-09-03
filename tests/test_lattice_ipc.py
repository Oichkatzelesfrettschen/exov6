import os
import subprocess
import tempfile
import pathlib
import textwrap

# C compiler to use when building C snippets.
CC = os.environ.get("CC", "clang")
# Repository root for header includes.
ROOT = pathlib.Path(__file__).resolve().parents[1]

C_CODE = textwrap.dedent(
    """
#include <assert.h>
#include <stdint.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/wait.h>
#include <unistd.h>
#include "include/lattice_ipc.h"
#include "include/exokernel.h"

struct mailbox {
    int has;
    char buf[8];
    size_t len;
};
static struct mailbox *mb;

static int exo_send(exo_cap dest, const void *buf, uint64_t len){
    struct mailbox *m = &mb[dest.id];
    m->len = len < sizeof(m->buf) ? len : sizeof(m->buf);
    memcpy(m->buf, buf, m->len);
    m->has = 1;
    (void)dest.rights;
    return 0;
}

static int exo_recv(exo_cap src, void *buf, uint64_t len){
    struct mailbox *m = &mb[src.id];
    if(!m->has) return 0;
    size_t n = m->len < len ? m->len : len;
    memcpy(buf, m->buf, n);
    m->has = 0;
    (void)src.rights;
    return (int)n;
}

static struct exo_ipc_ops ops = { exo_send, exo_recv };

int main(void){
    mb = mmap(NULL, sizeof(struct mailbox)*2, PROT_READ|PROT_WRITE,
              MAP_ANON|MAP_SHARED, -1, 0);
    assert(mb != MAP_FAILED);
    memset(mb,0,sizeof(struct mailbox)*2);
    exo_ipc_register(&ops);

    lattice_channel_t ch;
    exo_cap c = { .id=0, .rights=EXO_RIGHT_R|EXO_RIGHT_W };
    assert(lattice_connect(&ch, c) == 0);
    assert(atomic_load(&ch.seq) == 0);
    char buf[8];

    pid_t pid = fork();
    if(pid==0){
        int r = lattice_recv(&ch, buf, 2);
        assert(r==2);
        assert(buf[0]=='o' && buf[1]=='k');
        assert(atomic_load(&ch.seq) == 2);
        _exit(0);
    }

    char msg[3] = "ok";
    assert(lattice_send(&ch, msg, 2)==0);
    int st; waitpid(pid,&st,0);
    assert(atomic_load(&ch.seq) == 2);
    assert(st==0);

    assert(lattice_send(NULL, msg, 1)<0);
    assert(lattice_recv(NULL, buf, 1)<0);
    lattice_close(&ch);
    return 0;
}
""")

def compile_and_run(code: str) -> int:
    """Compile the provided C snippet and execute the resulting binary."""
    with tempfile.TemporaryDirectory() as td:
        src = pathlib.Path(td)/"test.c"
        exe = pathlib.Path(td)/"test"
        src.write_text(code)
        (pathlib.Path(td)/"types.h").write_text(
            "typedef unsigned int uint;\n"
            "typedef unsigned short ushort;\n"
            "typedef unsigned char uchar;\n"
            "typedef unsigned long uint64;\n"
            "typedef unsigned long uintptr;\n"
        )
        (pathlib.Path(td) / "defs.h").write_text("")
        (pathlib.Path(td) / "stdint.h").write_text(
            "#ifndef TEST_STDINT_H\n#define TEST_STDINT_H\n#include </usr/include/stdint.h>\n#endif\n"
        )
        subprocess.check_call([
            CC,
            "-std=c17",
            "-Wall",
            "-Werror",
            "-Wno-unused-function",
            "-I",
            str(td),
            "-I",
            str(ROOT),
            "-idirafter",
            str(ROOT / "include"),
            str(src),
            str(ROOT / "kernel/lattice_ipc.c"),
            str(ROOT / "kernel/exo_ipc.c"),
            "-o",
            str(exe),
        ])
        return subprocess.run([str(exe)]).returncode

# Variant program that forces send and receive failures to test error paths.
C_CODE_ERROR = textwrap.dedent(
    """
#include <assert.h>
#include <stdint.h>
#include <string.h>
#include <sys/mman.h>
#include "include/lattice_ipc.h"
#include "include/exokernel.h"

struct mailbox { int has; char buf[8]; size_t len; };
static struct mailbox *mb;

static int exo_send(exo_cap dest, const void *buf, uint64_t len) {
    if (dest.id >= 2) return -1; /* trigger send failure */
    struct mailbox *m = &mb[dest.id];
    m->len = len < sizeof m->buf ? len : sizeof m->buf;
    memcpy(m->buf, buf, m->len);
    m->has = 1;
    (void)dest.rights;
    return 0;
}

static int exo_recv(exo_cap src, void *buf, uint64_t len) {
    struct mailbox *m = &mb[src.id];
    if (!m->has) return -1; /* trigger receive failure */
    size_t n = m->len < len ? m->len : len;
    memcpy(buf, m->buf, n);
    m->has = 0;
    (void)src.rights;
    return (int)n;
}

static struct exo_ipc_ops ops = {exo_send, exo_recv};

int main(void) {
    mb = mmap(NULL, sizeof(struct mailbox) * 2, PROT_READ | PROT_WRITE,
              MAP_ANON | MAP_SHARED, -1, 0);
    assert(mb != MAP_FAILED);
    memset(mb, 0, sizeof(struct mailbox) * 2);
    exo_ipc_register(&ops);

    lattice_channel_t ch;
    exo_cap c = {.id = 2, .rights = EXO_RIGHT_R | EXO_RIGHT_W};
    assert(lattice_connect(&ch, c) == 0);
    char buf[8] = {0};
    char msg[3] = "er";
    assert(lattice_send(&ch, msg, 2) < 0);
    assert(lattice_recv(&ch, buf, sizeof buf) < 0);
    return 0;
}
"""
)

def test_lattice_ipc_basic() -> None:
    """Verify basic send/receive semantics."""
    assert compile_and_run(C_CODE) == 0


def test_lattice_ipc_errors() -> None:
    """Ensure send/recv failures propagate negative return codes."""
    assert compile_and_run(C_CODE_ERROR) == 0

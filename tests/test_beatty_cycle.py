import subprocess
import tempfile
import pathlib

ROOT = pathlib.Path(__file__).resolve().parents[1]

C_CODE = r"""
#include <stdlib.h>
#include <string.h>

typedef struct dag_node dag_node;
struct dag_node_list { dag_node *node; struct dag_node_list *next; };
struct dag_node {
    int pending;
    int priority;
    struct dag_node_list *children;
    dag_node *next;
    dag_node **deps;
    int ndeps;
    int done;
};

static void *kalloc(void) { return calloc(1, sizeof(struct dag_node_list)); }

static int path_exists(dag_node *s, dag_node *d, dag_node **st, size_t depth) {
    for (size_t i = 0; i < depth; ++i)
        if (st[i] == s)
            return 0;
    if (s == d)
        return 1;
    st[depth] = s;
    for (struct dag_node_list *l = s->children; l; l = l->next)
        if (path_exists(l->node, d, st, depth + 1))
            return 1;
    return 0;
}

static int creates_cycle(dag_node *n) {
    dag_node *stack[64];
    for (int i = 0; i < n->ndeps; ++i)
        if (path_exists(n->deps[i], n, stack, 0))
            return 1;
    return 0;
}

int dag_sched_submit(dag_node *n) {
    if (creates_cycle(n))
        return -1;
    return 0;
}

void dag_node_add_dep(dag_node *p, dag_node *c) {
    struct dag_node_list *l = kalloc();
    l->node = c;
    l->next = p->children;
    p->children = l;
    c->pending++;
    c->deps = realloc(c->deps, sizeof(dag_node *) * (c->ndeps + 1));
    c->deps[c->ndeps++] = p;
}

void dag_node_init(dag_node *n) { memset(n, 0, sizeof(*n)); }
"""


def test_beatty_cycle_detection():
    with tempfile.TemporaryDirectory() as td:
        src = pathlib.Path(td) / "test.c"
        exe = pathlib.Path(td) / "test"
        src.write_text(
            C_CODE
            + "\nint main(){dag_node a,b; dag_node_init(&a); dag_node_init(&b); dag_node_add_dep(&a,&b); dag_node_add_dep(&b,&a); return dag_sched_submit(&a)==-1?0:1;}"
        )
        subprocess.check_call(
            [
                "gcc",
                "-std=c17",
                "-Wall",
                "-Werror",
                str(src),
                "-o",
                str(exe),
            ]
        )
        assert subprocess.run([str(exe)]).returncode == 0

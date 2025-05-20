#include "dag.h"
#include "defs.h"
#include "spinlock.h"
#include "exo_stream.h"

static struct dag_node *dag_list;
static struct spinlock dag_lock;

static struct dag_node *find_ready(void) {
    struct dag_node *n;
    for (n = dag_list; n; n = n->next) {
        if (n->done)
            continue;
        int i;
        for (i = 0; i < n->ndeps; i++)
            if (!n->deps[i]->done)
                break;
        if (i == n->ndeps)
            return n;
    }
    return 0;
}

static void run_ready(void) {
    struct dag_node *n;
    acquire(&dag_lock);
    n = find_ready();
    release(&dag_lock);
    if (!n)
        return;
    exo_yield_to(n->ctx);
    acquire(&dag_lock);
    n->done = 1;
    release(&dag_lock);
}

static void dag_yield(void) { run_ready(); }
static void dag_halt(void) { run_ready(); }

static struct exo_sched_ops dag_ops = {
    .halt = dag_halt,
    .yield = dag_yield,
    .next = 0,
};

void dag_sched_init(struct exo_stream *stream) {
    initlock(&dag_lock, "dag");
    dag_ops.next = stream->head;
    stream->head = &dag_ops;
}

void dag_submit(struct dag_node *list) {
    acquire(&dag_lock);
    if (!dag_list)
        dag_list = list;
    else {
        struct dag_node *t = dag_list;
        while (t->next)
            t = t->next;
        t->next = list;
    }
    for (struct dag_node *n = list; n; n = n->next)
        n->done = 0;
    release(&dag_lock);
}

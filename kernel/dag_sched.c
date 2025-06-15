/*
 * @file dag_sched.c
 * @brief DAG-based scheduler integrating Lattice IPC for cooperative yield.
 */

#include "types.h"
#include "defs.h"           /* kalloc, panic, etc. */
#include "spinlock.h"       /* struct spinlock, initlock, acquire, release */
#include "dag.h"            /* struct dag_node, struct dag_node_list */
#include "lattice_ipc.h"    /* lattice_yield_to() */
#include "exo_stream.h"     /* exo_stream_register() */
#include "exo_cpu.h"        /* exo_yield_to() */
#include <string.h>         /* memset */
#include <stdint.h>         /* standard integer types */
#include <stdbool.h>        /* bool */

/* Maximum depth for DFS in cycle detection */
#define DAG_MAX_DEPTH 64

/* Global scheduler state */
static struct spinlock   dag_lock;
static struct dag_node  *ready_head = NULL;

/* Helper container for DFS traversal */
struct node_vec {
    struct dag_node *data[DAG_MAX_DEPTH];
    size_t           len;
};

/* Forward declarations */
static bool node_vec_contains(const struct node_vec *v, struct dag_node *n);
static bool node_vec_push   (struct node_vec       *v, struct dag_node *n);
static bool dfs_path        (struct dag_node       *src,
                             struct dag_node       *dst,
                             struct node_vec       *stack,
                             struct node_vec       *visited);
static bool path_exists     (struct dag_node       *src,
                             struct dag_node       *dst);
static bool creates_cycle   (const struct dag_node *n);
static void enqueue_ready   (struct dag_node       *n);
static struct dag_node *dequeue_ready(void);
static void dag_mark_done   (struct dag_node       *n);
static void dag_halt        (void);

/*----------------------------------------------------------------------------*/
/* Public API                                                                */
/*----------------------------------------------------------------------------*/

/**
 * @brief Initialize a DAG node.
 */
void
dag_node_init(struct dag_node *n, exo_cap ctx)
{
    memset(n, 0, sizeof(*n));
    n->ctx      = ctx;
    n->priority = 0;
    n->chan     = NULL;
}

/**
 * @brief Set a node's scheduling priority.
 */
void
dag_node_set_priority(struct dag_node *n, int priority)
{
    n->priority = priority;
}

/**
 * @brief Attach a Lattice IPC channel to a node for yielding.
 */
void
dag_node_set_channel(struct dag_node *n, lattice_channel_t *chan)
{
    n->chan = chan;
}

/**
 * @brief Declare that @p child depends on @p parent.
 */
void
dag_node_add_dep(struct dag_node *parent, struct dag_node *child)
{
    struct dag_node_list *link = kalloc(sizeof(*link));
    if (!link) {
        panic("dag_node_add_dep: out of memory");
        return;
    }
    link->node = child;
    link->next = parent->children;
    parent->children = link;
    child->pending++;
    if (!child->deps) {
        child->deps = kalloc(sizeof(*child->deps) * DAG_MAX_DEPTH);
        child->ndeps = 0;
    }
    if (child->ndeps < DAG_MAX_DEPTH) {
        child->deps[child->ndeps++] = parent;
    }
}

/**
 * @brief Submit node @p n to the scheduler (if no cycles).
 */
int
dag_sched_submit(struct dag_node *n)
{
    acquire(&dag_lock);
    if (creates_cycle(n)) {
        release(&dag_lock);
        return -1;
    }
    if (n->pending == 0 && !n->done) {
        enqueue_ready(n);
    }
    release(&dag_lock);
    return 0;
}

/**
 * @brief Yield control to the next ready node.
 */
static void
dag_yield(void)
{
    struct dag_node *n;

    acquire(&dag_lock);
    n = dequeue_ready();
    release(&dag_lock);

    if (!n) {
        return;
    }

    if (n->chan) {
        lattice_yield_to(n->chan);
    } else {
        exo_yield_to(n->ctx);
    }

    acquire(&dag_lock);
    dag_mark_done(n);
    release(&dag_lock);
}

/**
 * @brief Yield to a specific node @p n if it is ready.
 */
void
dag_yield_to(struct dag_node *n)
{
    if (!n) {
        return;
    }

    acquire(&dag_lock);
    if (n->pending > 0 || n->done) {
        release(&dag_lock);
        return;
    }
    release(&dag_lock);

    exo_yield_to(n->ctx);

    acquire(&dag_lock);
    dag_mark_done(n);
    release(&dag_lock);
}

/**
 * @brief Initialize the DAG scheduler.
 */
void
dag_sched_init(void)
{
    initlock(&dag_lock, "dag");
    static struct exo_sched_ops ops = {
        .halt  = dag_halt,
        .yield = dag_yield,
        .next  = NULL
    };
    static struct exo_stream stream = {
        .head = &ops
    };
    exo_stream_register(&stream);
}

/*----------------------------------------------------------------------------*/
/* Static Helpers                                                            */
/*----------------------------------------------------------------------------*/

static bool
node_vec_contains(const struct node_vec *v, struct dag_node *n)
{
    for (size_t i = 0; i < v->len; ++i) {
        if (v->data[i] == n) {
            return true;
        }
    }
    return false;
}

static bool
node_vec_push(struct node_vec *v, struct dag_node *n)
{
    if (v->len >= DAG_MAX_DEPTH) {
        return false;
    }
    v->data[v->len++] = n;
    return true;
}

static bool
dfs_path(struct dag_node *src,
         struct dag_node *dst,
         struct node_vec *stack,
         struct node_vec *visited)
{
    if (node_vec_contains(stack, src)) {
        return true; /* back‐edge => cycle */
    }
    if (node_vec_contains(visited, src)) {
        return false;
    }
    if (!node_vec_push(stack, src)) {
        return true; /* depth overflow => treat as cycle */
    }
    node_vec_push(visited, src);
    if (src == dst) {
        return true;
    }
    for (struct dag_node_list *l = src->children; l; l = l->next) {
        if (dfs_path(l->node, dst, stack, visited)) {
            return true;
        }
    }
    stack->len--;
    return false;
}

static bool
path_exists(struct dag_node *src, struct dag_node *dst)
{
    struct node_vec stack   = { .len = 0 };
    struct node_vec visited = { .len = 0 };
    return dfs_path(src, dst, &stack, &visited);
}

static bool
creates_cycle(const struct dag_node *n)
{
    for (size_t i = 0; i < n->ndeps; ++i) {
        if (path_exists(n->deps[i], (struct dag_node *)n)) {
            return true;
        }
    }
    return false;
}

static inline int
node_weight(const struct dag_node *n)
{
    return n->priority;
}

static void
enqueue_ready(struct dag_node *n)
{
    struct dag_node **pp = &ready_head;
    int w = node_weight(n);
    while (*pp && node_weight(*pp) >= w) {
        pp = &(*pp)->next;
    }
    n->next = *pp;
    *pp     = n;
}

static struct dag_node *
dequeue_ready(void)
{
    struct dag_node *n = ready_head;
    if (n) {
        ready_head = n->next;
    }
    return n;
}

static void
dag_mark_done(struct dag_node *n)
{
    n->done = true;
    for (struct dag_node_list *l = n->children; l; l = l->next) {
        struct dag_node *child = l->node;
        if (--child->pending == 0) {
            enqueue_ready(child);
        }
    }
}

static void
dag_halt(void)
{
    /* No‐op */
}

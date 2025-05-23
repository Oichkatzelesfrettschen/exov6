#include "types.h"
#include "defs.h"
#include "spinlock.h"
#include "exo_stream.h"
#include "exo_cpu.h"

static struct spinlock beatty_lock;
static struct exo_sched_ops beatty_ops;
static struct exo_stream beatty_stream;

static exo_cap *tasks;
static double *weights;
static uint64 *counts;
static int ntasks;

void beatty_sched_set_tasks(const exo_cap *t, const double *w, int n) {
  acquire(&beatty_lock);

  if (tasks)
    kfree((char *)tasks);
  if (weights)
    kfree((char *)weights);
  if (counts)
    kfree((char *)counts);

  tasks = 0;
  weights = 0;
  counts = 0;
  ntasks = 0;

  if (n <= 0 || n * sizeof(exo_cap) > PGSIZE || n * sizeof(double) > PGSIZE ||
      n * sizeof(uint64) > PGSIZE) {
    release(&beatty_lock);
    return;
  }

  tasks = (exo_cap *)kalloc();
  weights = (double *)kalloc();
  counts = (uint64 *)kalloc();
  if (!tasks || !weights || !counts) {
    if (tasks)
      kfree((char *)tasks);
    if (weights)
      kfree((char *)weights);
    if (counts)
      kfree((char *)counts);
    tasks = 0;
    weights = 0;
    counts = 0;
    release(&beatty_lock);
    return;
  }

  memmove(tasks, t, n * sizeof(exo_cap));
  memmove(weights, w, n * sizeof(double));
  for (int i = 0; i < n; i++)
    counts[i] = 1;

  ntasks = n;

  release(&beatty_lock);
}

static void beatty_halt(void) { /* nothing */ }

static void beatty_yield(void) {
  acquire(&beatty_lock);
  exo_cap next = {0};
  if (ntasks > 0) {
    int idx = 0;
    uint64 best = (uint64)(weights[0] * (double)counts[0]);
    for (int i = 1; i < ntasks; i++) {
      uint64 v = (uint64)(weights[i] * (double)counts[i]);
      if (v < best) {
        best = v;
        idx = i;
      }
    }
    next = tasks[idx];
    counts[idx]++;
  }
  release(&beatty_lock);

  if (next.pa)
    exo_yield_to(next);
}

void beatty_sched_init(void) {
  initlock(&beatty_lock, "beatty");
  tasks = 0;
  weights = 0;
  counts = 0;
  ntasks = 0;
  beatty_ops.halt = beatty_halt;
  beatty_ops.yield = beatty_yield;
  beatty_ops.next = 0;
  beatty_stream.head = &beatty_ops;
  exo_stream_register(&beatty_stream);
}

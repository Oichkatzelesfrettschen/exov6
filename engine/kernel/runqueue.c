#include "types.h"
#include "defs.h"
#include "proc.h"
#include "runqueue.h"

struct proc *runqueue_head = 0;
struct proc *runqueue_tail = 0;

// Add process to run queue tail. Caller must hold ptable.lock (and sched_lock if
// modifying p->state).
void setrunqueue(struct proc *p) {
  if (p->rq_next || p->rq_prev || runqueue_head == p)
    return; // already queued
  p->rq_next = 0;
  p->rq_prev = runqueue_tail;
  if (runqueue_tail)
    runqueue_tail->rq_next = p;
  else
    runqueue_head = p;
  runqueue_tail = p;
}

// Remove process from run queue. Caller must hold ptable.lock.
void remrq(struct proc *p) {
  if (p->rq_prev)
    p->rq_prev->rq_next = p->rq_next;
  else
    runqueue_head = p->rq_next;
  if (p->rq_next)
    p->rq_next->rq_prev = p->rq_prev;
  else
    runqueue_tail = p->rq_prev;
  p->rq_next = 0;
  p->rq_prev = 0;
}

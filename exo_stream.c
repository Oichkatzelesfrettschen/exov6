#include "exo_stream.h"
#include "defs.h"
#include "spinlock.h"

static struct exo_stream *active_stream;

void exo_stream_register(struct exo_stream *stream) { active_stream = stream; }

static void default_halt(void) { asm volatile("hlt"); }

void exo_stream_halt(void) {
  struct exo_sched_ops *m;

  if (!active_stream) {
    default_halt();
    return;
  }
  for (m = active_stream->head; m; m = m->next)
    if (m->halt)
      m->halt();
}

void exo_stream_yield(void) {
  struct exo_sched_ops *m;

  if (!active_stream)
    return;
  for (m = active_stream->head; m; m = m->next)
    if (m->yield)
      m->yield();
}

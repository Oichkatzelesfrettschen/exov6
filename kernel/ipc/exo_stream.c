#include "exo_stream.h"
#include "defs.h"
#include "spinlock.h"

static struct exo_stream *active_stream;
static struct spinlock streamlock;

void exo_stream_register(struct exo_stream *stream) {
  static int inited;
  if (!inited) {
    initlock(&streamlock, "stream");
    inited = 1;
  }
  acquire(&streamlock);
  active_stream = stream;
  release(&streamlock);
}

static void default_halt(void) { __asm__ volatile("hlt"); }

void exo_stream_halt(void) {
  struct exo_sched_ops *m;

  acquire(&streamlock);
  if (!active_stream) {
    release(&streamlock);
    default_halt();
    return;
  }
  for (m = active_stream->head; m; m = m->next)
    if (m->halt)
      m->halt();
  release(&streamlock);
}

void exo_stream_yield(void) {
  struct exo_sched_ops *m;

  acquire(&streamlock);
  if (!active_stream) {
    release(&streamlock);
    return;
  }
  for (m = active_stream->head; m; m = m->next)
    if (m->yield)
      m->yield();
  release(&streamlock);
}

// Placeholder for hot-swapping schedulers
void exo_stream_hot_swap(struct exo_stream *new_stream) {
    acquire(&streamlock);
    // In a real implementation, this would involve:
    // 1. Gracefully stopping the active_stream (e.g., allowing current tasks to finish).
    // 2. Transferring any necessary state from active_stream to new_stream (e.g., runnable queues).
    // 3. Setting new_stream as the active_stream.
    // 4. Potentially deactivating/unloading the old stream.
    cprintf("exo_stream_hot_swap: Attempting to hot-swap scheduler stream.\n");
    active_stream = new_stream; // Simple swap for placeholder
    release(&streamlock);
}


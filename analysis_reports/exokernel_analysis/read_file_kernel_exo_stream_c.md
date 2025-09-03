# Analysis Report: `read_file` for `kernel/exo_stream.c`

## Tool Call:
```
default_api.read_file(absolute_path = "/Users/eirikr/Documents/GitHub/exov6/kernel/exo_stream.c")
```

## Output:
```c
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

static void default_halt(void) { asm volatile("hlt"); }

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
```
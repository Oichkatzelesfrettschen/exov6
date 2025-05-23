#include "streams.h"
#include "defs.h"
#include "spinlock.h"

static struct spinlock stream_lock;
static int inited;

static void stream_init(void) {
  if (!inited) {
    initlock(&stream_lock, "streams");
    inited = 1;
  }
}

void attach_module(queue_t *head, struct stream_ops *mod) {
  stream_init();
  acquire(&stream_lock);
  mod->next = head->head;
  head->head = mod;
  release(&stream_lock);
}

#include "file.h"
#include "fs.h"
#include "include/exokernel.h"
#include <string.h>
#include "sleeplock.h"
#include "spinlock.h"
#include "types.h"
#include "user.h"

// Basic wrappers to illustrate linking a user-space filesystem library.

static struct file dummy_file;

static int fifo_read(struct fifo *q, char *buf, size_t n) {
  size_t i = 0;
  while (i < n && q->rpos != q->wpos) {
    buf[i++] = q->data[q->rpos % sizeof(q->data)];
    q->rpos++;
  }
  return (int)i;
}

static int fifo_write(struct fifo *q, const char *buf, size_t n) {
  size_t i = 0;
  while (i < n && q->wpos - q->rpos < sizeof(q->data)) {
    q->data[q->wpos % sizeof(q->data)] = buf[i++];
    q->wpos++;
  }
  return (int)i;
}

void fileinit(void) {}

struct file *filealloc(void) {
  struct file *f = malloc(sizeof(struct file));
  if (!f)
    return 0;
  memset(f, 0, sizeof(*f));
  f->ref = 1;
  f->type = FD_NONE;
  return f;
}

struct file *filedup(struct file *f) {
  if (f)
    f->ref++;
  return f;
}

void fileclose(struct file *f) {
  if (!f)
    return;
  if (--f->ref == 0)
    free(f);
}

int filestat(struct file *f, struct stat *st) {
  if (!f || !st)
    return -1;
  if (f->type == FD_FIFO)
    st->size = 0;
  else
    st->size = BSIZE;
  return 0;
}

int fileread(struct file *f, char *addr, size_t n) {
  if (!f || !addr)
    return -1;
  if (f->type == FD_FIFO)
    return fifo_read(f->fifo, addr, n);
  int r = exo_read_disk(f->cap, addr, f->off, n);
  if (r > 0)
    f->off += r;
  return r;
}

int filewrite(struct file *f, char *addr, size_t n) {
  if (!f || !addr)
    return -1;
  if (f->type == FD_FIFO)
    return fifo_write(f->fifo, addr, n);
  int r = exo_write_disk(f->cap, addr, f->off, n);
  if (r > 0)
    f->off += r;
  return r;
}

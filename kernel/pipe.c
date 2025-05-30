#include "types.h"
#include "defs.h"
#include "param.h"
#include "mmu.h"
#include "proc.h"
#include "fs.h"
#include "spinlock.h"
#include "sleeplock.h"
#include "file.h"
#include "fcntl.h"

#define PIPESIZE 512

struct pipe {
  struct spinlock lock;
  char data[PIPESIZE];
  size_t nread;  // number of bytes read
  size_t nwrite; // number of bytes written
  int readopen;  // read fd is still open
  int writeopen; // write fd is still open
  exo_cap cap;
};

[[nodiscard]] int pipealloc(struct file **f0, struct file **f1) {
  struct pipe *p;

  p = 0;
  *f0 = *f1 = 0;
  if ((*f0 = filealloc()) == 0 || (*f1 = filealloc()) == 0)
    goto bad;
  exo_cap cap;
  if ((p = (struct pipe *)cap_kalloc(&cap)) == 0)
    goto bad;
  p->cap = cap;
  p->readopen = 1;
  p->writeopen = 1;
  p->nwrite = 0;
  p->nread = 0;
  initlock(&p->lock, "pipe");
  (*f0)->type = FD_PIPE;
  (*f0)->readable = 1;
  (*f0)->writable = 0;
  (*f0)->flags = 0;
  (*f0)->pipe = p;
  (*f1)->type = FD_PIPE;
  (*f1)->readable = 0;
  (*f1)->writable = 1;
  (*f1)->flags = 0;
  (*f1)->pipe = p;
  return 0;

  // PAGEBREAK: 20
bad:
  if (p)
    cap_kfree(p->cap);
  if (*f0)
    fileclose(*f0);
  if (*f1)
    fileclose(*f1);
  return -1;
}

void pipeclose(struct pipe *p, int writable) {
  acquire(&p->lock);
  if (writable) {
    p->writeopen = 0;
    wakeup(&p->nread);
  } else {
    p->readopen = 0;
    wakeup(&p->nwrite);
  }
  if (p->readopen == 0 && p->writeopen == 0) {
    release(&p->lock);
    cap_kfree(p->cap);
  } else
    release(&p->lock);
}

// PAGEBREAK: 40
int pipewrite(struct pipe *p, struct file *f, char *addr, size_t n) {
  size_t i;

  acquire(&p->lock);
  for (i = 0; i < n; i++) {
    while (p->nwrite == p->nread + PIPESIZE) { // DOC: pipewrite-full
      if (f->flags & O_NONBLOCK) {
        release(&p->lock);
        return i;
      }
      if (p->readopen == 0 || myproc()->killed) {
        release(&p->lock);
        return -1;
      }
      wakeup(&p->nread);
      sleep(&p->nwrite, &p->lock); // DOC: pipewrite-sleep
    }
    p->data[p->nwrite++ % PIPESIZE] = addr[i];
  }
  wakeup(&p->nread); // DOC: pipewrite-wakeup1
  release(&p->lock);
  return n;
}

int piperead(struct pipe *p, struct file *f, char *addr, size_t n) {
  size_t i;

  acquire(&p->lock);
  while (p->nread == p->nwrite && p->writeopen) { // DOC: pipe-empty
    if (f->flags & O_NONBLOCK) {
      release(&p->lock);
      return 0;
    }
    if (myproc()->killed) {
      release(&p->lock);
      return -1;
    }
    sleep(&p->nread, &p->lock); // DOC: piperead-sleep
  }
  for (i = 0; i < n; i++) { // DOC: piperead-copy
    if (p->nread == p->nwrite)
      break;
    addr[i] = p->data[p->nread++ % PIPESIZE];
  }
  wakeup(&p->nwrite); // DOC: piperead-wakeup
  release(&p->lock);
  return i;
}

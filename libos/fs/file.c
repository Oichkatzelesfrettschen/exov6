#include "file.h"
#include "fs.h"
#include "exokernel.h"
#include "sleeplock.h"
#include "spinlock.h"
#include "types.h"
#include <sys/stat.h>
#include <stdlib.h>

// Basic wrappers to illustrate linking a user-space filesystem library.


void fileinit(void) {}

struct file *filealloc(void) {
  struct file *f = malloc(sizeof(struct file));
  if (!f)
    return 0;
  *f = (struct file){.type = FD_CAP, .ref = 1, .sizep = 0};
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
  if (f->sizep)
    st->st_size = *f->sizep;
  else
    st->st_size = BSIZE; // minimal single-block file
  return 0;
}

int fileread(struct file *f, char *addr, size_t n) {
  if (!f || !addr)
    return -1;
  if (f->sizep && f->off >= *f->sizep)
    return 0;
  if (f->sizep && f->off + n > *f->sizep)
    n = *f->sizep - f->off;
  int r = exo_read_disk(f->cap, addr, f->off, n);
  if (r > 0)
    f->off += r;
  return r;
}

int filewrite(struct file *f, char *addr, size_t n) {
  if (!f || !addr)
    return -1;
  int r = exo_write_disk(f->cap, addr, f->off, n);
  if (r > 0)
    f->off += r;
  if (r > 0 && f->sizep && f->off > *f->sizep)
    *f->sizep = f->off;
  return r;
}

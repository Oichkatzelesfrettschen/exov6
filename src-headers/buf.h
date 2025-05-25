#pragma once

struct buf {
  int flags;
  uint32_t dev;
  uint32_t blockno;
  struct sleeplock lock;
  size_t refcnt;
  size_t rcref; // number of read-side references
  struct buf *prev; // LRU cache list
  struct buf *next;
  struct buf *qnext; // disk queue
  uint8_t data[BSIZE];
};
#define B_VALID 0x2  // buffer has been read from disk
#define B_DIRTY 0x4  // buffer needs to be written to disk


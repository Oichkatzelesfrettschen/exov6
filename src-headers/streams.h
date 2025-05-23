#pragma once
#include "types.h"

typedef struct mblk {
  struct mblk *next;
  struct mblk *prev;
  char *base;
  char *lim;
  char *rp;
  char *wp;
} mblk_t;

struct stream_ops;

typedef struct queue {
  struct stream_ops *head;
} queue_t;

struct stream_ops {
  void (*open)(queue_t *);
  void (*close)(queue_t *);
  void (*put)(queue_t *, mblk_t *);
  void (*service)(queue_t *);
  struct stream_ops *next;
};

void attach_module(queue_t *head, struct stream_ops *mod);

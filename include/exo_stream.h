#pragma once
#include "types.h"

struct exo_sched_ops {
  void (*halt)(void);
  void (*yield)(void);
  struct exo_sched_ops *next;
};

struct exo_stream {
  struct exo_sched_ops *head;
};

/*
 * Access to the global active stream pointer is protected by a spinlock
 * defined in exo_stream.c.  The register, halt and yield helpers acquire
 * and release this lock internally.
 */

void exo_stream_register(struct exo_stream *stream);
void exo_stream_halt(void);
void exo_stream_yield(void);
#pragma once
#include "types.h"

struct exo_sched_ops {
  void (*halt)(void);
  void (*yield)(void);
  struct exo_sched_ops *next;
};

struct exo_stream {
  struct exo_sched_ops *head;
};

void exo_stream_register(struct exo_stream *stream);
void exo_stream_halt(void);
void exo_stream_yield(void);

#include "libos/posix.h"
#include "caplib.h"
#include <stdlib.h>
#include <string.h>

struct libos_mq {
  exo_cap cap;
};

libos_mqd_t mq_open(const char *name, int flags) {
  (void)name;
  (void)flags;
  struct libos_mq *q = malloc(sizeof(*q));
  if (!q)
    return NULL;
  q->cap = cap_alloc_page();
  return q;
}

int mq_send(libos_mqd_t q, const char *buf, size_t len, unsigned prio) {
  (void)prio;
  if (!q)
    return -1;
  return cap_send(q->cap, buf, len);
}

int mq_receive(libos_mqd_t q, char *buf, size_t len, unsigned *prio) {
  (void)prio;
  if (!q)
    return -1;
  return cap_recv(q->cap, buf, len);
}

int mq_close(libos_mqd_t q) {
  if (!q)
    return -1;
  cap_unbind_page(q->cap);
  free(q);
  return 0;
}

struct libos_sem {
  exo_cap cap;
  unsigned value;
};

libos_sem_t sem_open(const char *name, int flags, unsigned value) {
  (void)name;
  (void)flags;
  struct libos_sem *s = malloc(sizeof(*s));
  if (!s)
    return NULL;
  s->cap = cap_alloc_page();
  s->value = value;
  return s;
}

int sem_wait(libos_sem_t s) {
  if (!s)
    return -1;
  if (s->value == 0)
    return -1;
  s->value--;
  return 0;
}

int sem_post(libos_sem_t s) {
  if (!s)
    return -1;
  s->value++;
  return 0;
}

int sem_close(libos_sem_t s) {
  if (!s)
    return -1;
  cap_unbind_page(s->cap);
  free(s);
  return 0;
}

struct libos_shm {
  exo_cap cap;
  void *addr;
  size_t size;
};

libos_shm_t shm_open(const char *name, int flags, size_t size) {
  (void)name;
  (void)flags;
  struct libos_shm *s = malloc(sizeof(*s));
  if (!s)
    return NULL;
  s->cap = cap_alloc_page();
  s->addr = malloc(size);
  s->size = size;
  return s;
}

void *shm_map(libos_shm_t s) {
  if (!s)
    return NULL;
  return s->addr;
}

int shm_unmap(libos_shm_t s) {
  if (!s)
    return -1;
  return 0;
}

int shm_close(libos_shm_t s) {
  if (!s)
    return -1;
  free(s->addr);
  cap_unbind_page(s->cap);
  free(s);
  return 0;
}

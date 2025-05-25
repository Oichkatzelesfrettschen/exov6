#pragma once
#include <stdint.h>
#include "types.h"

#ifdef __cplusplus
extern "C" {
#endif

typedef struct {
    int pid;
} pthread_t;

typedef struct {
    volatile int locked;
} pthread_mutex_t;

static inline int pthread_mutex_init(pthread_mutex_t *m, const void *attr){
    (void)attr;
    if(!m) return -1;
    m->locked = 0;
    return 0;
}
int pthread_create(pthread_t *thread, const void *attr,
                   void *(*start_routine)(void*), void *arg);
int pthread_join(pthread_t thread, void **retval);
int pthread_mutex_lock(pthread_mutex_t *m);
int pthread_mutex_unlock(pthread_mutex_t *m);
static inline int pthread_mutex_destroy(pthread_mutex_t *m){ (void)m; return 0; }

#ifdef __cplusplus
}
#endif

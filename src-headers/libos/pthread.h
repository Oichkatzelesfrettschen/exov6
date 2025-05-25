#pragma once
#include <stddef.h>

typedef int pthread_t;

typedef struct {
  int dummy;
} pthread_attr_t;

int pthread_create(pthread_t *thread, const pthread_attr_t *attr,
                   void *(*start_routine)(void *), void *arg);
int pthread_join(pthread_t thread, void **retval);

typedef struct {
  volatile int locked;
} pthread_mutex_t;

typedef int pthread_mutexattr_t;

#define PTHREAD_MUTEX_INITIALIZER {0}

int pthread_mutex_init(pthread_mutex_t *m, const pthread_mutexattr_t *a);
int pthread_mutex_lock(pthread_mutex_t *m);
int pthread_mutex_unlock(pthread_mutex_t *m);
int pthread_mutex_destroy(pthread_mutex_t *m);

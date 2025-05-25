#include "pthread.h"
#include <unistd.h>
#include <sys/wait.h>

int pthread_create(pthread_t *thread, const pthread_attr_t *attr,
                   void *(*start_routine)(void *), void *arg) {
  (void)attr;
  pid_t pid = fork();
  if (pid < 0)
    return -1;
  if (pid == 0) {
    start_routine(arg);
    _exit(0);
  }
  if (thread)
    *thread = pid;
  return 0;
}

int pthread_join(pthread_t thread, void **retval) {
  (void)retval;
  return waitpid(thread, NULL, 0) < 0 ? -1 : 0;
}

int pthread_mutex_init(pthread_mutex_t *m, const pthread_mutexattr_t *a) {
  (void)a;
  m->locked = 0;
  return 0;
}

int pthread_mutex_lock(pthread_mutex_t *m) {
  while (__sync_lock_test_and_set(&m->locked, 1))
    sleep(0);
  return 0;
}

int pthread_mutex_unlock(pthread_mutex_t *m) {
  __sync_lock_release(&m->locked);
  return 0;
}

int pthread_mutex_destroy(pthread_mutex_t *m) {
  (void)m;
  return 0;
}

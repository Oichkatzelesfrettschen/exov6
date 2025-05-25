#include "libos/pthread.h"
#include "user.h"
#include <stdlib.h>
#include <unistd.h>
#include <sys/wait.h>

int pthread_create(pthread_t *thread, const void *attr,
                   void *(*start_routine)(void*), void *arg)
{
    (void)attr;
    int pid = fork();
    if(pid < 0)
        return -1;
    if(pid == 0){
        start_routine(arg);
        exit();
    }
    if(thread)
        thread->pid = pid;
    return 0;
}

int pthread_join(pthread_t t, void **retval)
{
    (void)retval;
    int status;
    while(waitpid(t.pid, &status, 0) < 0) {
        // retry if interrupted
    }
    return 0;
}

int pthread_mutex_lock(pthread_mutex_t *m)
{
    while(__sync_lock_test_and_set(&m->locked, 1))
        ;
    return 0;
}

int pthread_mutex_unlock(pthread_mutex_t *m)
{
    __sync_lock_release(&m->locked);
    return 0;
}

/* pthread_core.c - Core POSIX Threading Implementation */
#include <pthread.h>
#include <errno.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <sys/mman.h>
#include "exo.h"

/* Thread control block */
typedef struct pthread_tcb {
    pthread_t id;
    void *(*start_routine)(void *);
    void *arg;
    void *retval;
    int detached;
    int state;  /* RUNNING, FINISHED, CANCELED */
    struct pthread_tcb *next;
    exo_cap thread_cap;  /* Exokernel thread capability */
    void *stack_base;
    size_t stack_size;
    pthread_attr_t attr;
} pthread_tcb_t;

/* Thread states */
#define PTHREAD_STATE_RUNNING   0
#define PTHREAD_STATE_FINISHED  1
#define PTHREAD_STATE_CANCELED  2
#define PTHREAD_STATE_DETACHED  3

/* Global thread management */
static pthread_tcb_t *thread_list = NULL;
static pthread_t next_thread_id = 1;
static pthread_mutex_t thread_list_mutex = PTHREAD_MUTEX_INITIALIZER;

/* Thread-local storage */
static _Thread_local pthread_tcb_t *current_thread = NULL;
static _Thread_local pthread_key_t key_counter = 0;

#define MAX_KEYS 128
static void (*key_destructors[MAX_KEYS])(void *);
static _Thread_local void *key_values[MAX_KEYS];

/* Mutex implementation using exokernel primitives */
typedef struct {
    int locked;
    pthread_t owner;
    int type;
    int count;  /* For recursive mutexes */
    exo_cap mutex_cap;
} mutex_impl_t;

/* Condition variable implementation */
typedef struct {
    int waiters;
    exo_cap cond_cap;
} cond_impl_t;

/* Helper functions */
static pthread_tcb_t *find_thread(pthread_t thread) {
    pthread_tcb_t *tcb = thread_list;
    while (tcb && tcb->id != thread) {
        tcb = tcb->next;
    }
    return tcb;
}

static void add_thread(pthread_tcb_t *tcb) {
    pthread_mutex_lock(&thread_list_mutex);
    tcb->next = thread_list;
    thread_list = tcb;
    pthread_mutex_unlock(&thread_list_mutex);
}

static void remove_thread(pthread_tcb_t *tcb) {
    pthread_mutex_lock(&thread_list_mutex);
    if (thread_list == tcb) {
        thread_list = tcb->next;
    } else {
        pthread_tcb_t *prev = thread_list;
        while (prev && prev->next != tcb) {
            prev = prev->next;
        }
        if (prev) {
            prev->next = tcb->next;
        }
    }
    pthread_mutex_unlock(&thread_list_mutex);
}

/* Thread wrapper function */
static void thread_wrapper(void *arg) {
    pthread_tcb_t *tcb = (pthread_tcb_t *)arg;
    current_thread = tcb;
    
    /* Call the actual thread function */
    tcb->retval = tcb->start_routine(tcb->arg);
    
    /* Mark as finished */
    tcb->state = PTHREAD_STATE_FINISHED;
    
    /* If detached, clean up immediately */
    if (tcb->detached) {
        remove_thread(tcb);
        if (tcb->stack_base) {
            munmap(tcb->stack_base, tcb->stack_size);
        }
        free(tcb);
    }
    
    /* Exit thread via exokernel */
    exo_yield_to(0);  /* Never returns */
}

/* POSIX thread creation */
int pthread_create(pthread_t *thread, const pthread_attr_t *attr,
                  void *(*start_routine)(void *), void *arg) {
    if (!thread || !start_routine) {
        return EINVAL;
    }
    
    pthread_tcb_t *tcb = calloc(1, sizeof(pthread_tcb_t));
    if (!tcb) {
        return ENOMEM;
    }
    
    tcb->id = __sync_fetch_and_add(&next_thread_id, 1);
    tcb->start_routine = start_routine;
    tcb->arg = arg;
    tcb->state = PTHREAD_STATE_RUNNING;
    
    /* Set attributes */
    if (attr) {
        tcb->attr = *attr;
    } else {
        pthread_attr_init(&tcb->attr);
    }
    
    /* Allocate stack */
    size_t stack_size = 0;
    pthread_attr_getstacksize(&tcb->attr, &stack_size);
    if (stack_size == 0) {
        stack_size = 8192;  /* Default stack size */
    }
    
    tcb->stack_base = mmap(NULL, stack_size, PROT_READ | PROT_WRITE,
                          MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    if (tcb->stack_base == MAP_FAILED) {
        free(tcb);
        return ENOMEM;
    }
    tcb->stack_size = stack_size;
    
    /* Check if detached */
    int detachstate;
    pthread_attr_getdetachstate(&tcb->attr, &detachstate);
    tcb->detached = (detachstate == PTHREAD_CREATE_DETACHED);
    
    add_thread(tcb);
    
    /* Create exokernel thread - simplified for now */
    /* This would use exokernel-specific thread creation */
    tcb->thread_cap = exo_alloc_page();  /* Placeholder - use proper thread creation */
    
    /* For now, simulate thread creation by using fork() */
    pid_t pid = fork();
    if (pid == 0) {
        /* Child process acts as thread */
        thread_wrapper(tcb);
        exit(0);  /* Should not reach here */
    } else if (pid > 0) {
        /* Parent continues */
        *thread = tcb->id;
        return 0;
    } else {
        /* Fork failed */
        remove_thread(tcb);
        munmap(tcb->stack_base, tcb->stack_size);
        free(tcb);
        return EAGAIN;
    }
}

/* Thread joining */
int pthread_join(pthread_t thread, void **retval) {
    pthread_tcb_t *tcb = find_thread(thread);
    if (!tcb) {
        return ESRCH;
    }
    
    if (tcb->detached) {
        return EINVAL;
    }
    
    /* Wait for thread to finish */
    while (tcb->state == PTHREAD_STATE_RUNNING) {
        exo_yield_to(0);  /* Yield and check again */
        usleep(1000);     /* Small delay */
    }
    
    if (retval) {
        *retval = tcb->retval;
    }
    
    /* Clean up */
    remove_thread(tcb);
    if (tcb->stack_base) {
        munmap(tcb->stack_base, tcb->stack_size);
    }
    free(tcb);
    
    return 0;
}

/* Thread detaching */
int pthread_detach(pthread_t thread) {
    pthread_tcb_t *tcb = find_thread(thread);
    if (!tcb) {
        return ESRCH;
    }
    
    if (tcb->detached) {
        return EINVAL;
    }
    
    tcb->detached = 1;
    return 0;
}

/* Thread exit */
void pthread_exit(void *retval) {
    if (current_thread) {
        current_thread->retval = retval;
        current_thread->state = PTHREAD_STATE_FINISHED;
        
        /* Call key destructors */
        for (int i = 0; i < MAX_KEYS; i++) {
            if (key_values[i] && key_destructors[i]) {
                key_destructors[i](key_values[i]);
            }
        }
    }
    
    exit(0);  /* Exit the process (thread) */
}

/* Get current thread ID */
pthread_t pthread_self(void) {
    if (current_thread) {
        return current_thread->id;
    }
    return 1;  /* Main thread */
}

/* Compare thread IDs */
int pthread_equal(pthread_t t1, pthread_t t2) {
    return t1 == t2;
}

/* Thread attributes */
int pthread_attr_init(pthread_attr_t *attr) {
    if (!attr) return EINVAL;
    
    memset(attr, 0, sizeof(*attr));
    /* Set defaults */
    *(int *)(&attr->__size[0]) = PTHREAD_CREATE_JOINABLE;  /* detachstate */
    *(size_t *)(&attr->__size[4]) = 8192;                  /* stacksize */
    
    return 0;
}

int pthread_attr_destroy(pthread_attr_t *attr) {
    (void)attr;
    return 0;  /* Nothing to cleanup */
}

int pthread_attr_setdetachstate(pthread_attr_t *attr, int detachstate) {
    if (!attr || (detachstate != PTHREAD_CREATE_DETACHED && 
                  detachstate != PTHREAD_CREATE_JOINABLE)) {
        return EINVAL;
    }
    
    *(int *)(&attr->__size[0]) = detachstate;
    return 0;
}

int pthread_attr_getdetachstate(const pthread_attr_t *attr, int *detachstate) {
    if (!attr || !detachstate) return EINVAL;
    
    *detachstate = *(int *)(&attr->__size[0]);
    return 0;
}

int pthread_attr_setstacksize(pthread_attr_t *attr, size_t stacksize) {
    if (!attr || stacksize < PTHREAD_STACK_MIN) {
        return EINVAL;
    }
    
    *(size_t *)(&attr->__size[4]) = stacksize;
    return 0;
}

int pthread_attr_getstacksize(const pthread_attr_t *attr, size_t *stacksize) {
    if (!attr || !stacksize) return EINVAL;
    
    *stacksize = *(size_t *)(&attr->__size[4]);
    return 0;
}

/* Thread-specific data */
int pthread_key_create(pthread_key_t *key, void (*destructor)(void *)) {
    if (!key) return EINVAL;
    
    pthread_key_t new_key = __sync_fetch_and_add(&key_counter, 1);
    if (new_key >= MAX_KEYS) {
        return EAGAIN;
    }
    
    key_destructors[new_key] = destructor;
    *key = new_key;
    return 0;
}

int pthread_key_delete(pthread_key_t key) {
    if (key >= MAX_KEYS) return EINVAL;
    
    key_destructors[key] = NULL;
    return 0;
}

void *pthread_getspecific(pthread_key_t key) {
    if (key >= MAX_KEYS) return NULL;
    
    return key_values[key];
}

int pthread_setspecific(pthread_key_t key, const void *value) {
    if (key >= MAX_KEYS) return EINVAL;
    
    key_values[key] = (void *)value;
    return 0;
}

/* One-time initialization */
int pthread_once(pthread_once_t *once_control, void (*init_routine)(void)) {
    if (!once_control || !init_routine) return EINVAL;
    
    static pthread_mutex_t once_mutex = PTHREAD_MUTEX_INITIALIZER;
    
    if (__sync_bool_compare_and_swap(&once_control->__i[0], 0, 1)) {
        init_routine();
        __sync_synchronize();
        once_control->__i[0] = 2;
    } else {
        while (once_control->__i[0] == 1) {
            usleep(1000);  /* Spin-wait */
        }
    }
    
    return 0;
}
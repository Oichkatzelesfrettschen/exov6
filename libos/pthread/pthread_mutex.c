/* pthread_mutex.c - POSIX Mutex Implementation using Exokernel primitives */
#include <pthread.h>
#include <errno.h>
#include <string.h>
#include <stdlib.h>
#include <time.h>
#include <unistd.h>
#include "exo.h"

/* Internal mutex structure */
typedef struct {
    volatile int locked;
    pthread_t owner;
    int type;
    int count;          /* For recursive mutexes */
    int robust;
    int pshared;
    int protocol;
    int prioceiling;
    exo_cap mutex_cap;  /* Exokernel synchronization primitive */
} mutex_impl_t;

/* Get mutex implementation from opaque type */
static inline mutex_impl_t *get_mutex_impl(pthread_mutex_t *mutex) {
    return (mutex_impl_t *)mutex;
}

/* Initialize mutex implementation */
static void init_mutex_impl(mutex_impl_t *impl, const pthread_mutexattr_t *attr) {
    impl->locked = 0;
    impl->owner = 0;
    impl->count = 0;
    impl->type = PTHREAD_MUTEX_NORMAL;
    impl->robust = PTHREAD_MUTEX_STALLED;
    impl->pshared = PTHREAD_PROCESS_PRIVATE;
    impl->protocol = PTHREAD_PRIO_NONE;
    impl->prioceiling = 0;
    
    if (attr) {
        pthread_mutexattr_gettype(attr, &impl->type);
        pthread_mutexattr_getrobust(attr, &impl->robust);
        pthread_mutexattr_getpshared(attr, &impl->pshared);
        pthread_mutexattr_getprotocol(attr, &impl->protocol);
        pthread_mutexattr_getprioceiling(attr, &impl->prioceiling);
    }
    
    /* Allocate exokernel synchronization primitive */
    impl->mutex_cap = exo_alloc_page(); /* Placeholder - use proper sync primitive */
}

/* Mutex operations */
int pthread_mutex_init(pthread_mutex_t *mutex, const pthread_mutexattr_t *attr) {
    if (!mutex) return EINVAL;
    
    mutex_impl_t *impl = get_mutex_impl(mutex);
    init_mutex_impl(impl, attr);
    
    return 0;
}

int pthread_mutex_destroy(pthread_mutex_t *mutex) {
    if (!mutex) return EINVAL;
    
    mutex_impl_t *impl = get_mutex_impl(mutex);
    
    if (impl->locked) {
        return EBUSY;
    }
    
    /* Release exokernel resources */
    if (impl->mutex_cap.id != 0) {
        exo_unbind_page(impl->mutex_cap);
    }
    
    memset(impl, 0, sizeof(*impl));
    return 0;
}

int pthread_mutex_lock(pthread_mutex_t *mutex) {
    if (!mutex) return EINVAL;
    
    mutex_impl_t *impl = get_mutex_impl(mutex);
    pthread_t self = pthread_self();
    
    /* Handle different mutex types */
    switch (impl->type) {
    case PTHREAD_MUTEX_NORMAL:
        /* Simple lock - may deadlock if same thread locks twice */
        while (__sync_val_compare_and_swap(&impl->locked, 0, 1) != 0) {
            exo_cap sched_cap = pthread_get_scheduler_cap(self);
            exo_yield_to(sched_cap);  /* Yield to scheduler */
        }
        impl->owner = self;
        break;
        
    case PTHREAD_MUTEX_RECURSIVE:
        if (impl->owner == self) {
            /* Same thread - increment count */
            impl->count++;
            return 0;
        }
        /* Fall through for first lock */
        while (__sync_val_compare_and_swap(&impl->locked, 0, 1) != 0) {
            exo_cap sched_cap = pthread_get_scheduler_cap(self);
            exo_yield_to(sched_cap);
        }
        impl->owner = self;
        impl->count = 1;
        break;
        
    case PTHREAD_MUTEX_ERRORCHECK:
        if (impl->owner == self) {
            return EDEADLK;  /* Would deadlock */
        }
        while (__sync_val_compare_and_swap(&impl->locked, 0, 1) != 0) {
            exo_cap sched_cap = pthread_get_scheduler_cap(self);
            exo_yield_to(sched_cap);
        }
        impl->owner = self;
        break;
        
    default:
        return EINVAL;
    }
    
    return 0;
}

int pthread_mutex_trylock(pthread_mutex_t *mutex) {
    if (!mutex) return EINVAL;
    
    mutex_impl_t *impl = get_mutex_impl(mutex);
    pthread_t self = pthread_self();
    
    switch (impl->type) {
    case PTHREAD_MUTEX_NORMAL:
        if (__sync_val_compare_and_swap(&impl->locked, 0, 1) == 0) {
            impl->owner = self;
            return 0;
        }
        return EBUSY;
        
    case PTHREAD_MUTEX_RECURSIVE:
        if (impl->owner == self) {
            impl->count++;
            return 0;
        }
        if (__sync_val_compare_and_swap(&impl->locked, 0, 1) == 0) {
            impl->owner = self;
            impl->count = 1;
            return 0;
        }
        return EBUSY;
        
    case PTHREAD_MUTEX_ERRORCHECK:
        if (impl->owner == self) {
            return EDEADLK;
        }
        if (__sync_val_compare_and_swap(&impl->locked, 0, 1) == 0) {
            impl->owner = self;
            return 0;
        }
        return EBUSY;
        
    default:
        return EINVAL;
    }
}

int pthread_mutex_unlock(pthread_mutex_t *mutex) {
    if (!mutex) return EINVAL;
    
    mutex_impl_t *impl = get_mutex_impl(mutex);
    pthread_t self = pthread_self();
    
    switch (impl->type) {
    case PTHREAD_MUTEX_NORMAL:
        /* Normal mutex - no ownership checking */
        impl->owner = 0;
        __sync_lock_release(&impl->locked);
        break;
        
    case PTHREAD_MUTEX_RECURSIVE:
        if (impl->owner != self) {
            return EPERM;  /* Not the owner */
        }
        if (--impl->count == 0) {
            impl->owner = 0;
            __sync_lock_release(&impl->locked);
        }
        break;
        
    case PTHREAD_MUTEX_ERRORCHECK:
        if (impl->owner != self) {
            return EPERM;  /* Not the owner */
        }
        impl->owner = 0;
        __sync_lock_release(&impl->locked);
        break;
        
    default:
        return EINVAL;
    }
    
    return 0;
}

int pthread_mutex_timedlock(pthread_mutex_t *mutex, const struct timespec *abs_timeout) {
    if (!mutex || !abs_timeout) return EINVAL;
    
    /* Get current time */
    struct timespec now;
    clock_gettime(CLOCK_REALTIME, &now);
    
    /* Check if already timed out */
    if (now.tv_sec > abs_timeout->tv_sec || 
        (now.tv_sec == abs_timeout->tv_sec && now.tv_nsec >= abs_timeout->tv_nsec)) {
        return ETIMEDOUT;
    }
    
    /* Try to lock with timeout - simplified implementation */
    int max_attempts = 1000;  /* Approximate timeout handling */
    for (int i = 0; i < max_attempts; i++) {
        int result = pthread_mutex_trylock(mutex);
        if (result != EBUSY) {
            return result;
        }
        
        /* Check timeout again */
        clock_gettime(CLOCK_REALTIME, &now);
        if (now.tv_sec > abs_timeout->tv_sec || 
            (now.tv_sec == abs_timeout->tv_sec && now.tv_nsec >= abs_timeout->tv_nsec)) {
            return ETIMEDOUT;
        }
        
        usleep(1000);  /* Sleep for 1ms */
    }
    
    return ETIMEDOUT;
}

/* Mutex attributes */
int pthread_mutexattr_init(pthread_mutexattr_t *attr) {
    if (!attr) return EINVAL;
    
    /* Initialize to defaults */
    int *data = (int *)attr;
    data[0] = PTHREAD_MUTEX_NORMAL;     /* type */
    data[1] = PTHREAD_PROCESS_PRIVATE;  /* pshared */
    data[2] = PTHREAD_PRIO_NONE;        /* protocol */
    data[3] = 0;                        /* prioceiling */
    data[4] = PTHREAD_MUTEX_STALLED;    /* robust */
    
    return 0;
}

int pthread_mutexattr_destroy(pthread_mutexattr_t *attr) {
    (void)attr;
    return 0;  /* Nothing to cleanup */
}

int pthread_mutexattr_settype(pthread_mutexattr_t *attr, int type) {
    if (!attr) return EINVAL;
    
    if (type != PTHREAD_MUTEX_NORMAL && 
        type != PTHREAD_MUTEX_RECURSIVE && 
        type != PTHREAD_MUTEX_ERRORCHECK) {
        return EINVAL;
    }
    
    ((int *)attr)[0] = type;
    return 0;
}

int pthread_mutexattr_gettype(const pthread_mutexattr_t *attr, int *type) {
    if (!attr || !type) return EINVAL;
    
    *type = ((int *)attr)[0];
    return 0;
}

int pthread_mutexattr_setpshared(pthread_mutexattr_t *attr, int pshared) {
    if (!attr) return EINVAL;
    
    if (pshared != PTHREAD_PROCESS_PRIVATE && pshared != PTHREAD_PROCESS_SHARED) {
        return EINVAL;
    }
    
    ((int *)attr)[1] = pshared;
    return 0;
}

int pthread_mutexattr_getpshared(const pthread_mutexattr_t *attr, int *pshared) {
    if (!attr || !pshared) return EINVAL;
    
    *pshared = ((int *)attr)[1];
    return 0;
}

int pthread_mutexattr_setprotocol(pthread_mutexattr_t *attr, int protocol) {
    if (!attr) return EINVAL;
    
    if (protocol != PTHREAD_PRIO_NONE && 
        protocol != PTHREAD_PRIO_INHERIT && 
        protocol != PTHREAD_PRIO_PROTECT) {
        return EINVAL;
    }
    
    ((int *)attr)[2] = protocol;
    return 0;
}

int pthread_mutexattr_getprotocol(const pthread_mutexattr_t *attr, int *protocol) {
    if (!attr || !protocol) return EINVAL;
    
    *protocol = ((int *)attr)[2];
    return 0;
}

int pthread_mutexattr_setprioceiling(pthread_mutexattr_t *attr, int prioceiling) {
    if (!attr || prioceiling < 0) return EINVAL;
    
    ((int *)attr)[3] = prioceiling;
    return 0;
}

int pthread_mutexattr_getprioceiling(const pthread_mutexattr_t *attr, int *prioceiling) {
    if (!attr || !prioceiling) return EINVAL;
    
    *prioceiling = ((int *)attr)[3];
    return 0;
}

int pthread_mutexattr_setrobust(pthread_mutexattr_t *attr, int robust) {
    if (!attr) return EINVAL;
    
    if (robust != PTHREAD_MUTEX_STALLED && robust != PTHREAD_MUTEX_ROBUST) {
        return EINVAL;
    }
    
    ((int *)attr)[4] = robust;
    return 0;
}

int pthread_mutexattr_getrobust(const pthread_mutexattr_t *attr, int *robust) {
    if (!attr || !robust) return EINVAL;
    
    *robust = ((int *)attr)[4];
    return 0;
}

/* Robust mutex recovery */
int pthread_mutex_consistent(pthread_mutex_t *mutex) {
    if (!mutex) return EINVAL;
    
    mutex_impl_t *impl = get_mutex_impl(mutex);
    
    if (impl->robust != PTHREAD_MUTEX_ROBUST) {
        return EINVAL;
    }
    
    /* Mark mutex as consistent - simplified implementation */
    impl->owner = pthread_self();
    return 0;
}

/* Priority ceiling functions */
int pthread_mutex_setprioceiling(pthread_mutex_t *mutex, int prioceiling, int *old_ceiling) {
    if (!mutex || prioceiling < 0) return EINVAL;
    
    mutex_impl_t *impl = get_mutex_impl(mutex);
    
    if (old_ceiling) {
        *old_ceiling = impl->prioceiling;
    }
    
    impl->prioceiling = prioceiling;
    return 0;
}

int pthread_mutex_getprioceiling(const pthread_mutex_t *mutex, int *prioceiling) {
    if (!mutex || !prioceiling) return EINVAL;
    
    const mutex_impl_t *impl = (const mutex_impl_t *)mutex;
    *prioceiling = impl->prioceiling;
    return 0;
}
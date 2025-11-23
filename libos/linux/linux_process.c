/**
 * @file linux_process.c
 * @brief Linux Process and Thread Syscalls
 *
 * Implements Linux process/thread creation and management syscalls.
 * Key syscalls: clone, clone3, fork, vfork, execve, exit, wait4, futex
 *
 * Threading model follows Linux semantics:
 * - Threads are tasks sharing resources via CLONE_* flags
 * - Thread groups (tgid) represent processes
 * - Individual tasks have unique tid
 *
 * References:
 * - https://eli.thegreenplace.net/2018/launching-linux-threads-and-processes-with-clone/
 * - https://eli.thegreenplace.net/2018/basics-of-futexes/
 * - https://man7.org/linux/man-pages/man2/clone.2.html
 */

#include "linux_syscall.h"
#include <errno.h>
#include <string.h>
#include <stdlib.h>
#include <stdatomic.h>

/*
 * ============================================================================
 * Thread Control Block (TCB) for Linux ABI
 * ============================================================================
 */

#define MAX_THREADS         1024
#define STACK_SIZE_DEFAULT  (2 * 1024 * 1024)  /* 2MB default stack */

/* Thread/task states */
#define TASK_RUNNING        0
#define TASK_INTERRUPTIBLE  1
#define TASK_UNINTERRUPTIBLE 2
#define TASK_STOPPED        4
#define TASK_ZOMBIE         8
#define TASK_DEAD           16

/* Thread structure */
struct linux_task {
    /* Identity */
    int32_t             tid;            /* Thread ID (unique) */
    int32_t             tgid;           /* Thread group ID (= pid of main thread) */
    int32_t             ppid;           /* Parent process ID */
    int32_t             pgid;           /* Process group ID */
    int32_t             sid;            /* Session ID */

    /* State */
    _Atomic(int)        state;
    _Atomic(int)        exit_code;
    int                 exit_signal;

    /* Thread Local Storage */
    void               *tls;
    void               *stack_base;
    size_t              stack_size;

    /* Synchronization */
    int                *clear_child_tid; /* Cleared and futex woken on exit */
    int                *set_child_tid;   /* Set on clone */
    struct linux_robust_list_head *robust_list;

    /* Resource sharing (from clone flags) */
    unsigned long       clone_flags;

    /* Parent/child linkage */
    struct linux_task  *parent;
    struct linux_task  *children;
    struct linux_task  *sibling;

    /* Credentials */
    uint32_t            uid, gid;
    uint32_t            euid, egid;
    uint32_t            suid, sgid;

    /* Signal handling */
    uint64_t            signal_mask;
    uint64_t            signal_pending;
    struct linux_sigaction sighand[LINUX_NSIG];

    /* CPU affinity */
    uint64_t            cpu_affinity;

    /* Scheduling */
    int                 policy;
    int                 priority;
    int                 nice;
};

/* Task table */
static struct linux_task *task_table[MAX_THREADS];
static _Atomic(int32_t) next_tid = 1;
static struct linux_task *current_task = NULL;

/* Lock for task table operations */
static _Atomic(int) task_lock = 0;

static void lock_tasks(void) {
    int expected = 0;
    while (!atomic_compare_exchange_weak(&task_lock, &expected, 1)) {
        expected = 0;
        /* Spin */
    }
}

static void unlock_tasks(void) {
    atomic_store(&task_lock, 0);
}

/*
 * ============================================================================
 * Task Management
 * ============================================================================
 */

static struct linux_task *alloc_task(void)
{
    struct linux_task *task = calloc(1, sizeof(*task));
    if (task == NULL)
        return NULL;

    task->tid = atomic_fetch_add(&next_tid, 1);
    task->state = TASK_RUNNING;
    task->cpu_affinity = ~0ULL;  /* All CPUs */
    task->policy = 0;            /* SCHED_OTHER */
    task->priority = 0;

    /* Add to task table */
    lock_tasks();
    if (task->tid < MAX_THREADS) {
        task_table[task->tid] = task;
    }
    unlock_tasks();

    return task;
}

static void free_task(struct linux_task *task)
{
    if (task == NULL)
        return;

    lock_tasks();
    if (task->tid < MAX_THREADS) {
        task_table[task->tid] = NULL;
    }
    unlock_tasks();

    if (task->stack_base && !(task->clone_flags & CLONE_VM)) {
        free(task->stack_base);
    }

    free(task);
}

static struct linux_task *find_task(int tid)
{
    if (tid < 0 || tid >= MAX_THREADS)
        return NULL;
    return task_table[tid];
}

static struct linux_task *get_current(void)
{
    if (current_task == NULL) {
        /* Create initial task */
        current_task = alloc_task();
        if (current_task) {
            current_task->tgid = current_task->tid;
            current_task->ppid = 0;
            current_task->pgid = current_task->tgid;
            current_task->sid = current_task->tgid;
        }
    }
    return current_task;
}

/*
 * ============================================================================
 * Clone Implementation
 * ============================================================================
 */

/**
 * linux_sys_clone - Create a new process/thread
 * @flags: CLONE_* flags controlling resource sharing
 * @stack: New stack pointer for child
 * @parent_tid: Pointer to store child TID in parent
 * @child_tid: Pointer to store child TID in child
 * @tls: Thread Local Storage pointer
 *
 * This is the core syscall for both fork() and pthread_create().
 * The flags determine what resources are shared vs copied.
 */
long linux_sys_clone(unsigned long flags, void *stack, int *parent_tid,
                     int *child_tid, unsigned long tls)
{
    struct linux_task *parent = get_current();
    struct linux_task *child;
    int exit_signal = flags & 0xff;  /* Low byte is signal */

    flags &= ~0xff;  /* Remove signal from flags */

    if (parent == NULL)
        return -EAGAIN;

    /* Validate flag combinations */
    if ((flags & CLONE_THREAD) && !(flags & CLONE_SIGHAND))
        return -EINVAL;
    if ((flags & CLONE_SIGHAND) && !(flags & CLONE_VM))
        return -EINVAL;

    /* Allocate new task */
    child = alloc_task();
    if (child == NULL)
        return -ENOMEM;

    /* Set up identity */
    child->clone_flags = flags;
    child->exit_signal = exit_signal;
    child->parent = parent;

    if (flags & CLONE_THREAD) {
        /* Thread: same thread group */
        child->tgid = parent->tgid;
    } else {
        /* Process: new thread group */
        child->tgid = child->tid;
    }

    if (flags & CLONE_PARENT) {
        child->ppid = parent->ppid;
    } else {
        child->ppid = parent->tgid;
    }

    child->pgid = parent->pgid;
    child->sid = parent->sid;

    /* Copy credentials */
    child->uid = parent->uid;
    child->gid = parent->gid;
    child->euid = parent->euid;
    child->egid = parent->egid;
    child->suid = parent->suid;
    child->sgid = parent->sgid;

    /* Handle CLONE_VM - share virtual memory */
    if (!(flags & CLONE_VM)) {
        /* Would do COW memory copy here */
        /* For now, just note the flag */
    }

    /* Handle CLONE_SIGHAND - share signal handlers */
    if (flags & CLONE_SIGHAND) {
        memcpy(child->sighand, parent->sighand, sizeof(parent->sighand));
    } else {
        /* Copy signal handlers (they're separate) */
        memcpy(child->sighand, parent->sighand, sizeof(parent->sighand));
    }

    /* Handle CLONE_SETTLS - set thread local storage */
    if (flags & CLONE_SETTLS) {
        child->tls = (void *)tls;
    }

    /* Handle CLONE_PARENT_SETTID */
    if ((flags & CLONE_PARENT_SETTID) && parent_tid) {
        *parent_tid = child->tid;
    }

    /* Handle CLONE_CHILD_SETTID */
    if (flags & CLONE_CHILD_SETTID) {
        child->set_child_tid = child_tid;
        if (child_tid) {
            *child_tid = child->tid;
        }
    }

    /* Handle CLONE_CHILD_CLEARTID */
    if (flags & CLONE_CHILD_CLEARTID) {
        child->clear_child_tid = child_tid;
    }

    /* Set up stack */
    if (stack) {
        child->stack_base = stack;
        child->stack_size = STACK_SIZE_DEFAULT;
    } else if (!(flags & CLONE_VM)) {
        /* Allocate new stack for process */
        child->stack_base = malloc(STACK_SIZE_DEFAULT);
        child->stack_size = STACK_SIZE_DEFAULT;
    }

    /* Link to parent's children list */
    lock_tasks();
    child->sibling = parent->children;
    parent->children = child;
    unlock_tasks();

    /* In a real implementation, we would:
     * 1. Set up the child's CPU context
     * 2. Add it to the scheduler
     * 3. Return 0 in child, child->tid in parent
     *
     * For now, we just return the child TID
     */

    return child->tid;
}

/**
 * linux_sys_clone3 - Extended clone syscall (Linux 5.3+)
 * @args: Clone arguments structure
 * @size: Size of args structure
 */
long linux_sys_clone3(struct linux_clone_args *args, size_t size)
{
    if (args == NULL || size < sizeof(*args))
        return -EINVAL;

    return linux_sys_clone(args->flags | args->exit_signal,
                           (void *)args->stack,
                           (int *)args->parent_tid,
                           (int *)args->child_tid,
                           args->tls);
}

/*
 * ============================================================================
 * Fork/Vfork Implementation
 * ============================================================================
 */

/**
 * linux_sys_fork - Create a child process
 *
 * Equivalent to clone() with no sharing flags.
 */
long linux_sys_fork(void)
{
    return linux_sys_clone(LINUX_SIGCHLD, NULL, NULL, NULL, 0);
}

/**
 * linux_sys_vfork - Create child that shares memory until exec/exit
 *
 * Parent is suspended until child calls execve() or _exit().
 */
long linux_sys_vfork(void)
{
    return linux_sys_clone(CLONE_VFORK | CLONE_VM | LINUX_SIGCHLD,
                           NULL, NULL, NULL, 0);
}

/*
 * ============================================================================
 * Process Exit
 * ============================================================================
 */

/**
 * linux_sys_exit - Terminate the calling thread
 */
void linux_sys_exit(int status)
{
    struct linux_task *task = get_current();

    if (task == NULL)
        return;

    atomic_store(&task->exit_code, status);
    atomic_store(&task->state, TASK_ZOMBIE);

    /* Handle CLONE_CHILD_CLEARTID - clear tid and wake futex */
    if (task->clear_child_tid) {
        *task->clear_child_tid = 0;
        /* Wake any futex waiters */
        linux_sys_futex(task->clear_child_tid, FUTEX_WAKE, 1, NULL, NULL, 0);
    }

    /* Process robust futex list */
    if (task->robust_list) {
        /* Would walk robust list and wake waiters */
    }

    /* Reparent children to init (task 1) or parent */
    lock_tasks();
    struct linux_task *child = task->children;
    while (child) {
        struct linux_task *next = child->sibling;
        child->ppid = 1;  /* Reparent to init */
        child = next;
    }
    task->children = NULL;
    unlock_tasks();

    /* Signal parent if needed */
    if (task->parent && task->exit_signal) {
        task->parent->signal_pending |= (1ULL << task->exit_signal);
    }

    /* In real implementation, would remove from scheduler and yield */
}

/**
 * linux_sys_exit_group - Terminate all threads in thread group
 */
void linux_sys_exit_group(int status)
{
    struct linux_task *task = get_current();

    if (task == NULL)
        return;

    /* Signal all threads in group to exit */
    lock_tasks();
    for (int i = 0; i < MAX_THREADS; i++) {
        if (task_table[i] && task_table[i]->tgid == task->tgid) {
            atomic_store(&task_table[i]->exit_code, status);
            atomic_store(&task_table[i]->state, TASK_ZOMBIE);
        }
    }
    unlock_tasks();

    linux_sys_exit(status);
}

/*
 * ============================================================================
 * Wait for Process/Thread
 * ============================================================================
 */

/**
 * linux_sys_wait4 - Wait for process to change state
 */
long linux_sys_wait4(int pid, int *status, int options, struct linux_rusage *rusage)
{
    struct linux_task *task = get_current();
    struct linux_task *child = NULL;

    if (task == NULL)
        return -ECHILD;

    lock_tasks();

    if (pid > 0) {
        /* Wait for specific child */
        child = find_task(pid);
        if (child == NULL || child->ppid != task->tgid) {
            unlock_tasks();
            return -ECHILD;
        }
    } else if (pid == -1) {
        /* Wait for any child */
        child = task->children;
    } else if (pid == 0) {
        /* Wait for any child in same process group */
        for (struct linux_task *c = task->children; c; c = c->sibling) {
            if (c->pgid == task->pgid) {
                child = c;
                break;
            }
        }
    } else {
        /* Wait for any child in specified process group */
        for (struct linux_task *c = task->children; c; c = c->sibling) {
            if (c->pgid == -pid) {
                child = c;
                break;
            }
        }
    }

    if (child == NULL) {
        unlock_tasks();
        return -ECHILD;
    }

    /* Check if any child is zombie */
    struct linux_task *zombie = NULL;
    for (struct linux_task *c = (pid > 0) ? child : task->children; c; c = c->sibling) {
        if (atomic_load(&c->state) == TASK_ZOMBIE) {
            zombie = c;
            break;
        }
        if (pid > 0) break;  /* Only check specific child */
    }

    unlock_tasks();

    if (zombie == NULL) {
        if (options & 1 /* WNOHANG */)
            return 0;
        /* Would block here in real implementation */
        return -ECHILD;
    }

    /* Return status */
    if (status) {
        int code = atomic_load(&zombie->exit_code);
        *status = (code & 0xff) << 8;  /* Exit status in bits 8-15 */
    }

    if (rusage) {
        memset(rusage, 0, sizeof(*rusage));
    }

    int ret_pid = zombie->tid;

    /* Clean up zombie unless WNOWAIT */
    if (!(options & 0x01000000 /* __WALL */)) {
        /* Remove from children list */
        lock_tasks();
        struct linux_task **pp = &task->children;
        while (*pp) {
            if (*pp == zombie) {
                *pp = zombie->sibling;
                break;
            }
            pp = &(*pp)->sibling;
        }
        unlock_tasks();

        free_task(zombie);
    }

    return ret_pid;
}

/**
 * linux_sys_waitid - Wait for process (extended)
 */
long linux_sys_waitid(int which, int pid, void *infop, int options, struct linux_rusage *rusage)
{
    /* Convert to wait4 semantics */
    int wait_pid;

    switch (which) {
    case 0:  /* P_ALL */
        wait_pid = -1;
        break;
    case 1:  /* P_PID */
        wait_pid = pid;
        break;
    case 2:  /* P_PGID */
        wait_pid = -pid;
        break;
    default:
        return -EINVAL;
    }

    return linux_sys_wait4(wait_pid, NULL, options, rusage);
}

/*
 * ============================================================================
 * Process/Thread ID Queries
 * ============================================================================
 */

long linux_sys_getpid(void)
{
    struct linux_task *task = get_current();
    return task ? task->tgid : 1;
}

long linux_sys_gettid(void)
{
    struct linux_task *task = get_current();
    return task ? task->tid : 1;
}

long linux_sys_getppid(void)
{
    struct linux_task *task = get_current();
    return task ? task->ppid : 0;
}

long linux_sys_getpgid(int pid)
{
    struct linux_task *task;

    if (pid == 0) {
        task = get_current();
    } else {
        task = find_task(pid);
    }

    return task ? task->pgid : -ESRCH;
}

long linux_sys_setpgid(int pid, int pgid)
{
    struct linux_task *task;

    if (pid == 0) {
        task = get_current();
    } else {
        task = find_task(pid);
    }

    if (task == NULL)
        return -ESRCH;

    if (pgid == 0)
        pgid = task->tgid;

    task->pgid = pgid;
    return 0;
}

long linux_sys_getsid(int pid)
{
    struct linux_task *task;

    if (pid == 0) {
        task = get_current();
    } else {
        task = find_task(pid);
    }

    return task ? task->sid : -ESRCH;
}

long linux_sys_setsid(void)
{
    struct linux_task *task = get_current();

    if (task == NULL)
        return -EPERM;

    /* Can't create session if already a process group leader */
    if (task->tgid == task->pgid)
        return -EPERM;

    task->sid = task->tgid;
    task->pgid = task->tgid;

    return task->sid;
}

/*
 * ============================================================================
 * Thread ID Address & Robust List
 * ============================================================================
 */

long linux_sys_set_tid_address(int *tidptr)
{
    struct linux_task *task = get_current();

    if (task == NULL)
        return -ESRCH;

    task->clear_child_tid = tidptr;
    return task->tid;
}

long linux_sys_set_robust_list(struct linux_robust_list_head *head, size_t len)
{
    struct linux_task *task = get_current();

    if (task == NULL)
        return -ESRCH;

    if (len != sizeof(*head))
        return -EINVAL;

    task->robust_list = head;
    return 0;
}

long linux_sys_get_robust_list(int pid, struct linux_robust_list_head **head, size_t *len)
{
    struct linux_task *task;

    if (pid == 0) {
        task = get_current();
    } else {
        task = find_task(pid);
    }

    if (task == NULL)
        return -ESRCH;

    if (head)
        *head = task->robust_list;
    if (len)
        *len = sizeof(struct linux_robust_list_head);

    return 0;
}

/*
 * ============================================================================
 * Futex Implementation
 * ============================================================================
 */

#define FUTEX_HASH_SIZE     256

struct futex_waiter {
    int                    *uaddr;
    struct linux_task      *task;
    uint32_t                bitset;
    struct futex_waiter    *next;
};

static struct futex_waiter *futex_hash[FUTEX_HASH_SIZE];
static _Atomic(int) futex_lock = 0;

static void lock_futex(void) {
    int expected = 0;
    while (!atomic_compare_exchange_weak(&futex_lock, &expected, 1)) {
        expected = 0;
    }
}

static void unlock_futex(void) {
    atomic_store(&futex_lock, 0);
}

static unsigned int futex_hash_fn(int *uaddr)
{
    return ((unsigned long)uaddr >> 2) % FUTEX_HASH_SIZE;
}

/**
 * linux_sys_futex - Fast userspace mutex operations
 * @uaddr: Futex address
 * @op: Operation (FUTEX_WAIT, FUTEX_WAKE, etc.)
 * @val: Value (meaning depends on op)
 * @timeout: Timeout for wait operations
 * @uaddr2: Second address for requeue operations
 * @val3: Third value for some operations
 */
long linux_sys_futex(int *uaddr, int op, int val, const struct linux_timespec *timeout,
                     int *uaddr2, int val3)
{
    int cmd = op & ~(FUTEX_PRIVATE_FLAG | FUTEX_CLOCK_REALTIME);
    unsigned int hash;
    struct futex_waiter *waiter, **pp;
    int woken = 0;

    if (uaddr == NULL)
        return -EINVAL;

    hash = futex_hash_fn(uaddr);

    switch (cmd) {
    case FUTEX_WAIT:
    case FUTEX_WAIT_BITSET:
        {
            uint32_t bitset = (cmd == FUTEX_WAIT_BITSET) ? (uint32_t)val3 : FUTEX_BITSET_MATCH_ANY;

            if (bitset == 0)
                return -EINVAL;

            /* Check if value matches */
            if (*uaddr != val)
                return -EAGAIN;

            /* Add to wait queue */
            waiter = malloc(sizeof(*waiter));
            if (waiter == NULL)
                return -ENOMEM;

            waiter->uaddr = uaddr;
            waiter->task = get_current();
            waiter->bitset = bitset;

            lock_futex();
            waiter->next = futex_hash[hash];
            futex_hash[hash] = waiter;
            unlock_futex();

            /* In real implementation, would sleep here until:
             * 1. FUTEX_WAKE wakes us
             * 2. Timeout expires
             * 3. Signal interrupts us
             *
             * For now, just simulate immediate wakeup
             */

            /* Remove from wait queue (simulating wakeup) */
            lock_futex();
            pp = &futex_hash[hash];
            while (*pp) {
                if (*pp == waiter) {
                    *pp = waiter->next;
                    break;
                }
                pp = &(*pp)->next;
            }
            unlock_futex();

            free(waiter);
            return 0;
        }

    case FUTEX_WAKE:
    case FUTEX_WAKE_BITSET:
        {
            uint32_t bitset = (cmd == FUTEX_WAKE_BITSET) ? (uint32_t)val3 : FUTEX_BITSET_MATCH_ANY;

            if (bitset == 0)
                return -EINVAL;

            lock_futex();
            pp = &futex_hash[hash];
            while (*pp && woken < val) {
                waiter = *pp;
                if (waiter->uaddr == uaddr && (waiter->bitset & bitset)) {
                    /* Wake this waiter */
                    *pp = waiter->next;
                    /* In real implementation, would wake the task */
                    free(waiter);
                    woken++;
                } else {
                    pp = &(*pp)->next;
                }
            }
            unlock_futex();

            return woken;
        }

    case FUTEX_REQUEUE:
    case FUTEX_CMP_REQUEUE:
        {
            int requeued = 0;
            unsigned int hash2;

            if (cmd == FUTEX_CMP_REQUEUE && *uaddr != val3)
                return -EAGAIN;

            if (uaddr2 == NULL)
                return -EINVAL;

            hash2 = futex_hash_fn(uaddr2);

            lock_futex();

            /* Wake up to val waiters */
            pp = &futex_hash[hash];
            while (*pp && woken < val) {
                waiter = *pp;
                if (waiter->uaddr == uaddr) {
                    *pp = waiter->next;
                    free(waiter);
                    woken++;
                } else {
                    pp = &(*pp)->next;
                }
            }

            /* Requeue remaining waiters (up to val2) */
            pp = &futex_hash[hash];
            while (*pp && requeued < (int)(long)timeout) {  /* val2 passed via timeout */
                waiter = *pp;
                if (waiter->uaddr == uaddr) {
                    /* Move to uaddr2 */
                    *pp = waiter->next;
                    waiter->uaddr = uaddr2;
                    waiter->next = futex_hash[hash2];
                    futex_hash[hash2] = waiter;
                    requeued++;
                } else {
                    pp = &(*pp)->next;
                }
            }

            unlock_futex();
            return woken;
        }

    case FUTEX_WAKE_OP:
        {
            /* Atomically modify *uaddr2, then wake waiters on uaddr and uaddr2 */
            /* Simplified implementation */
            lock_futex();

            /* Wake on uaddr */
            pp = &futex_hash[hash];
            while (*pp && woken < val) {
                waiter = *pp;
                if (waiter->uaddr == uaddr) {
                    *pp = waiter->next;
                    free(waiter);
                    woken++;
                } else {
                    pp = &(*pp)->next;
                }
            }

            /* Would perform atomic op on uaddr2 here */

            /* Wake on uaddr2 if condition met */
            if (uaddr2) {
                unsigned int hash2 = futex_hash_fn(uaddr2);
                int woken2 = 0;
                pp = &futex_hash[hash2];
                while (*pp && woken2 < (int)(long)timeout) {
                    waiter = *pp;
                    if (waiter->uaddr == uaddr2) {
                        *pp = waiter->next;
                        free(waiter);
                        woken2++;
                    } else {
                        pp = &(*pp)->next;
                    }
                }
                woken += woken2;
            }

            unlock_futex();
            return woken;
        }

    default:
        return -ENOSYS;
    }
}

/*
 * ============================================================================
 * Execve (Stub)
 * ============================================================================
 */

long linux_sys_execve(const char *path, char *const argv[], char *const envp[])
{
    /* Would load new executable image */
    (void)path;
    (void)argv;
    (void)envp;
    return -ENOSYS;
}

long linux_sys_execveat(int dirfd, const char *path, char *const argv[],
                        char *const envp[], int flags)
{
    (void)dirfd;
    (void)path;
    (void)argv;
    (void)envp;
    (void)flags;
    return -ENOSYS;
}

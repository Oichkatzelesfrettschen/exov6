/**
 * @file linux_sysv_ipc.c
 * @brief Linux System V IPC syscall implementations
 *
 * This file implements System V IPC for the exokernel libOS layer:
 * - Shared Memory (shmget, shmat, shmdt, shmctl)
 * - Semaphores (semget, semop, semctl)
 * - Message Queues (msgget, msgsnd, msgrcv, msgctl)
 *
 * System V IPC is a legacy but widely-used IPC mechanism in Linux.
 * Many applications (databases, scientific computing) depend on it.
 */

#include "linux_syscall.h"
#include <stddef.h>
#include <stdint.h>
#include <stdbool.h>

/* Forward declarations for exokernel primitives */
extern void *exo_alloc_pages(size_t count);
extern void exo_free_pages(void *addr, size_t count);
extern uint64_t exo_get_time_ns(void);

/*============================================================================
 * IPC Constants
 *============================================================================*/

/* IPC flags */
#define IPC_CREAT       01000       /* Create if key doesn't exist */
#define IPC_EXCL        02000       /* Fail if key exists */
#define IPC_NOWAIT      04000       /* Don't wait */
#define IPC_PRIVATE     0           /* Private key */

/* IPC control commands */
#define IPC_RMID        0           /* Remove identifier */
#define IPC_SET         1           /* Set options */
#define IPC_STAT        2           /* Get options */
#define IPC_INFO        3           /* Get system-wide info */

/* Shared memory commands */
#define SHM_LOCK        11          /* Lock segment in memory */
#define SHM_UNLOCK      12          /* Unlock segment */
#define SHM_STAT        13          /* Stat by index */
#define SHM_INFO        14          /* System-wide info */
#define SHM_STAT_ANY    15          /* Stat any segment */

/* Shared memory flags for shmat */
#define SHM_RDONLY      010000      /* Read-only attach */
#define SHM_RND         020000      /* Round attach address */
#define SHM_REMAP       040000      /* Allow remap */
#define SHM_EXEC        0100000     /* Allow exec */

/* Semaphore commands */
#define GETPID          11          /* Get sempid */
#define GETVAL          12          /* Get semval */
#define GETALL          13          /* Get all semvals */
#define GETNCNT         14          /* Get semncnt */
#define GETZCNT         15          /* Get semzcnt */
#define SETVAL          16          /* Set semval */
#define SETALL          17          /* Set all semvals */
#define SEM_STAT        18          /* Stat by index */
#define SEM_INFO        19          /* System-wide info */
#define SEM_STAT_ANY    20          /* Stat any semaphore */

/* Message queue commands */
#define MSG_STAT        11          /* Stat by index */
#define MSG_INFO        12          /* System-wide info */
#define MSG_STAT_ANY    13          /* Stat any queue */
#define MSG_NOERROR     010000      /* Truncate message */
#define MSG_EXCEPT      020000      /* Recv any msg except specified type */
#define MSG_COPY        040000      /* Copy (don't remove) msg */

/* Limits */
#define SHMMAX          (4UL * 1024 * 1024 * 1024)  /* Max segment size (4GB) */
#define SHMMIN          1                           /* Min segment size */
#define SHMMNI          4096                        /* Max segments system-wide */
#define SHMSEG          4096                        /* Max segments per process */
#define SHMALL          (SHMMAX / 4096)             /* Max pages system-wide */

#define SEMMNI          32000       /* Max semaphore sets */
#define SEMMSL          32000       /* Max semaphores per set */
#define SEMMNS          (SEMMNI * SEMMSL)
#define SEMOPM          500         /* Max ops per semop call */
#define SEMVMX          32767       /* Max semaphore value */

#define MSGMNI          32000       /* Max message queues */
#define MSGMAX          8192        /* Max message size */
#define MSGMNB          16384       /* Max bytes in queue */

/*============================================================================
 * IPC Permission Structure
 *============================================================================*/

struct ipc_perm {
    uint32_t    key;            /* Key supplied to *get() */
    uint32_t    uid;            /* Owner's user ID */
    uint32_t    gid;            /* Owner's group ID */
    uint32_t    cuid;           /* Creator's user ID */
    uint32_t    cgid;           /* Creator's group ID */
    uint16_t    mode;           /* Permissions */
    uint16_t    seq;            /* Sequence number */
    uint64_t    _pad1;
    uint64_t    _pad2;
};

/*============================================================================
 * Shared Memory Implementation
 *============================================================================*/

/**
 * Shared memory segment descriptor
 */
struct shmid_ds {
    struct ipc_perm shm_perm;   /* Permissions */
    size_t      shm_segsz;      /* Segment size */
    uint64_t    shm_atime;      /* Last attach time */
    uint64_t    shm_dtime;      /* Last detach time */
    uint64_t    shm_ctime;      /* Last change time */
    int32_t     shm_cpid;       /* Creator PID */
    int32_t     shm_lpid;       /* Last operation PID */
    uint64_t    shm_nattch;     /* Number of attachments */
    uint64_t    _pad1;
    uint64_t    _pad2;
};

/**
 * Shared memory segment
 */
struct shm_segment {
    int id;                     /* Segment ID */
    uint32_t key;               /* Key */
    struct shmid_ds ds;         /* Descriptor */
    void *addr;                 /* Physical address */
    int refcount;               /* Reference count */
    bool in_use;                /* Is segment in use */
};

/* Shared memory segment table */
#define SHM_MAX_SEGMENTS 256
static struct shm_segment shm_segments[SHM_MAX_SEGMENTS];
static int shm_next_id = 1;

/**
 * Find shared memory segment by key
 */
static struct shm_segment *shm_find_by_key(uint32_t key)
{
    if (key == IPC_PRIVATE) {
        return NULL;
    }

    for (int i = 0; i < SHM_MAX_SEGMENTS; i++) {
        if (shm_segments[i].in_use && shm_segments[i].key == key) {
            return &shm_segments[i];
        }
    }
    return NULL;
}

/**
 * Find shared memory segment by ID
 */
static struct shm_segment *shm_find_by_id(int shmid)
{
    for (int i = 0; i < SHM_MAX_SEGMENTS; i++) {
        if (shm_segments[i].in_use && shm_segments[i].id == shmid) {
            return &shm_segments[i];
        }
    }
    return NULL;
}

/**
 * Allocate a new shared memory segment
 */
static struct shm_segment *shm_alloc(void)
{
    for (int i = 0; i < SHM_MAX_SEGMENTS; i++) {
        if (!shm_segments[i].in_use) {
            shm_segments[i].in_use = true;
            shm_segments[i].id = shm_next_id++;
            return &shm_segments[i];
        }
    }
    return NULL;
}

/**
 * Get shared memory segment
 */
long linux_sys_shmget(uint32_t key, size_t size, int shmflg)
{
    /* Check if segment exists */
    struct shm_segment *seg = shm_find_by_key(key);

    if (seg) {
        /* Segment exists */
        if ((shmflg & IPC_CREAT) && (shmflg & IPC_EXCL)) {
            return -LINUX_EEXIST;
        }
        return seg->id;
    }

    /* Create new segment */
    if (!(shmflg & IPC_CREAT) && key != IPC_PRIVATE) {
        return -LINUX_ENOENT;
    }

    if (size < SHMMIN || size > SHMMAX) {
        return -LINUX_EINVAL;
    }

    seg = shm_alloc();
    if (!seg) {
        return -LINUX_ENOSPC;
    }

    /* Allocate memory */
    size_t pages = (size + 4095) / 4096;
    void *addr = exo_alloc_pages(pages);
    if (!addr) {
        seg->in_use = false;
        return -LINUX_ENOMEM;
    }

    /* Initialize segment */
    seg->key = key;
    seg->addr = addr;
    seg->refcount = 0;
    seg->ds.shm_perm.key = key;
    seg->ds.shm_perm.mode = shmflg & 0777;
    seg->ds.shm_perm.uid = 0;  /* TODO: Get from process */
    seg->ds.shm_perm.gid = 0;
    seg->ds.shm_perm.cuid = 0;
    seg->ds.shm_perm.cgid = 0;
    seg->ds.shm_segsz = size;
    seg->ds.shm_cpid = 1;      /* TODO: Get from process */
    seg->ds.shm_lpid = 0;
    seg->ds.shm_nattch = 0;
    seg->ds.shm_atime = 0;
    seg->ds.shm_dtime = 0;
    seg->ds.shm_ctime = exo_get_time_ns() / 1000000000ULL;

    return seg->id;
}

/**
 * Attach shared memory segment
 */
long linux_sys_shmat(int shmid, const void *shmaddr, int shmflg)
{
    struct shm_segment *seg = shm_find_by_id(shmid);
    if (!seg) {
        return -LINUX_EINVAL;
    }

    void *addr;
    if (shmaddr) {
        /* User specified address */
        if (shmflg & SHM_RND) {
            addr = (void *)((uintptr_t)shmaddr & ~0xfff);
        } else {
            addr = (void *)shmaddr;
        }
        /* TODO: Map at specified address */
    } else {
        /* Use segment's address directly (simplified) */
        addr = seg->addr;
    }

    seg->refcount++;
    seg->ds.shm_nattch++;
    seg->ds.shm_lpid = 1;  /* TODO: Get from process */
    seg->ds.shm_atime = exo_get_time_ns() / 1000000000ULL;

    return (long)addr;
}

/**
 * Detach shared memory segment
 */
long linux_sys_shmdt(const void *shmaddr)
{
    /* Find segment by address */
    for (int i = 0; i < SHM_MAX_SEGMENTS; i++) {
        if (shm_segments[i].in_use && shm_segments[i].addr == shmaddr) {
            struct shm_segment *seg = &shm_segments[i];
            seg->refcount--;
            seg->ds.shm_nattch--;
            seg->ds.shm_lpid = 1;  /* TODO: Get from process */
            seg->ds.shm_dtime = exo_get_time_ns() / 1000000000ULL;
            return 0;
        }
    }

    return -LINUX_EINVAL;
}

/**
 * Shared memory control
 */
long linux_sys_shmctl(int shmid, int cmd, struct shmid_ds *buf)
{
    struct shm_segment *seg = shm_find_by_id(shmid);
    if (!seg && cmd != IPC_INFO && cmd != SHM_INFO) {
        return -LINUX_EINVAL;
    }

    switch (cmd) {
    case IPC_STAT:
    case SHM_STAT:
        if (!buf) return -LINUX_EFAULT;
        *buf = seg->ds;
        return 0;

    case IPC_SET:
        if (!buf) return -LINUX_EFAULT;
        seg->ds.shm_perm.uid = buf->shm_perm.uid;
        seg->ds.shm_perm.gid = buf->shm_perm.gid;
        seg->ds.shm_perm.mode = buf->shm_perm.mode & 0777;
        seg->ds.shm_ctime = exo_get_time_ns() / 1000000000ULL;
        return 0;

    case IPC_RMID:
        if (seg->ds.shm_nattch > 0) {
            /* Mark for deletion when all detach */
            /* For now, just fail if still attached */
            return -LINUX_EBUSY;
        }
        size_t pages = (seg->ds.shm_segsz + 4095) / 4096;
        exo_free_pages(seg->addr, pages);
        seg->in_use = false;
        return 0;

    case SHM_LOCK:
        /* Lock in memory - no-op for exokernel */
        return 0;

    case SHM_UNLOCK:
        return 0;

    case IPC_INFO:
    case SHM_INFO:
        /* Return system-wide info */
        if (!buf) return -LINUX_EFAULT;
        /* Fill with limits */
        return 0;

    default:
        return -LINUX_EINVAL;
    }
}

/*============================================================================
 * Semaphore Implementation
 *============================================================================*/

/**
 * Semaphore set descriptor
 */
struct semid_ds {
    struct ipc_perm sem_perm;   /* Permissions */
    uint64_t    sem_otime;      /* Last semop time */
    uint64_t    sem_ctime;      /* Creation/change time */
    uint64_t    sem_nsems;      /* Number of semaphores */
    uint64_t    _pad1;
    uint64_t    _pad2;
};

/**
 * Semaphore operation structure
 */
struct sembuf {
    uint16_t    sem_num;        /* Semaphore number */
    int16_t     sem_op;         /* Operation */
    int16_t     sem_flg;        /* Flags */
};

/**
 * Individual semaphore
 */
struct sem {
    int16_t     semval;         /* Current value */
    int16_t     sempid;         /* Last operation PID */
    uint16_t    semncnt;        /* Processes waiting for increase */
    uint16_t    semzcnt;        /* Processes waiting for zero */
};

/**
 * Semaphore set
 */
struct sem_set {
    int id;                     /* Set ID */
    uint32_t key;               /* Key */
    struct semid_ds ds;         /* Descriptor */
    struct sem *sems;           /* Array of semaphores */
    bool in_use;
};

/* Semaphore set table */
#define SEM_MAX_SETS 256
static struct sem_set sem_sets[SEM_MAX_SETS];
static int sem_next_id = 1;

/**
 * Find semaphore set by key
 */
static struct sem_set *sem_find_by_key(uint32_t key)
{
    if (key == IPC_PRIVATE) {
        return NULL;
    }

    for (int i = 0; i < SEM_MAX_SETS; i++) {
        if (sem_sets[i].in_use && sem_sets[i].key == key) {
            return &sem_sets[i];
        }
    }
    return NULL;
}

/**
 * Find semaphore set by ID
 */
static struct sem_set *sem_find_by_id(int semid)
{
    for (int i = 0; i < SEM_MAX_SETS; i++) {
        if (sem_sets[i].in_use && sem_sets[i].id == semid) {
            return &sem_sets[i];
        }
    }
    return NULL;
}

/**
 * Allocate semaphore set
 */
static struct sem_set *sem_alloc(void)
{
    for (int i = 0; i < SEM_MAX_SETS; i++) {
        if (!sem_sets[i].in_use) {
            sem_sets[i].in_use = true;
            sem_sets[i].id = sem_next_id++;
            return &sem_sets[i];
        }
    }
    return NULL;
}

/**
 * Get or create semaphore set
 */
long linux_sys_semget(uint32_t key, int nsems, int semflg)
{
    struct sem_set *set = sem_find_by_key(key);

    if (set) {
        if ((semflg & IPC_CREAT) && (semflg & IPC_EXCL)) {
            return -LINUX_EEXIST;
        }
        return set->id;
    }

    if (!(semflg & IPC_CREAT) && key != IPC_PRIVATE) {
        return -LINUX_ENOENT;
    }

    if (nsems < 1 || nsems > SEMMSL) {
        return -LINUX_EINVAL;
    }

    set = sem_alloc();
    if (!set) {
        return -LINUX_ENOSPC;
    }

    /* Allocate semaphore array */
    set->sems = (struct sem *)exo_alloc_pages((nsems * sizeof(struct sem) + 4095) / 4096);
    if (!set->sems) {
        set->in_use = false;
        return -LINUX_ENOMEM;
    }

    /* Initialize */
    set->key = key;
    set->ds.sem_perm.key = key;
    set->ds.sem_perm.mode = semflg & 0777;
    set->ds.sem_nsems = nsems;
    set->ds.sem_otime = 0;
    set->ds.sem_ctime = exo_get_time_ns() / 1000000000ULL;

    /* Initialize all semaphores to 0 */
    for (int i = 0; i < nsems; i++) {
        set->sems[i].semval = 0;
        set->sems[i].sempid = 0;
        set->sems[i].semncnt = 0;
        set->sems[i].semzcnt = 0;
    }

    return set->id;
}

/**
 * Perform semaphore operations
 */
long linux_sys_semop(int semid, struct sembuf *sops, size_t nsops)
{
    return linux_sys_semtimedop(semid, sops, nsops, NULL);
}

/**
 * Perform semaphore operations with timeout
 */
long linux_sys_semtimedop(int semid, struct sembuf *sops, size_t nsops,
                          const struct linux_timespec *timeout)
{
    struct sem_set *set = sem_find_by_id(semid);
    if (!set) {
        return -LINUX_EINVAL;
    }

    if (nsops > SEMOPM || !sops) {
        return -LINUX_EINVAL;
    }

    /* Calculate timeout deadline */
    uint64_t deadline = 0;
    if (timeout) {
        deadline = exo_get_time_ns() + timeout->tv_sec * 1000000000ULL + timeout->tv_nsec;
    }

    /* Validate all operations first */
    for (size_t i = 0; i < nsops; i++) {
        if (sops[i].sem_num >= set->ds.sem_nsems) {
            return -LINUX_EFBIG;
        }
    }

    /* Try to perform operations atomically */
    bool blocked;
    do {
        blocked = false;

        /* Check if all operations can proceed */
        for (size_t i = 0; i < nsops; i++) {
            struct sem *s = &set->sems[sops[i].sem_num];
            int16_t op = sops[i].sem_op;

            if (op > 0) {
                /* Can always add */
                continue;
            } else if (op == 0) {
                /* Wait for zero */
                if (s->semval != 0) {
                    blocked = true;
                    break;
                }
            } else {
                /* Subtract - check if possible */
                if (s->semval < -op) {
                    if (sops[i].sem_flg & IPC_NOWAIT) {
                        return -LINUX_EAGAIN;
                    }
                    blocked = true;
                    break;
                }
            }
        }

        if (blocked) {
            /* Check timeout */
            if (timeout && exo_get_time_ns() >= deadline) {
                return -LINUX_EAGAIN;
            }
            /* Yield and retry */
            extern int exo_thread_yield(void);
            exo_thread_yield();
        }
    } while (blocked);

    /* All operations can proceed - apply them */
    for (size_t i = 0; i < nsops; i++) {
        struct sem *s = &set->sems[sops[i].sem_num];
        int16_t op = sops[i].sem_op;

        if (op > 0) {
            s->semval += op;
            if (s->semval > SEMVMX) {
                s->semval = SEMVMX;
            }
        } else if (op < 0) {
            s->semval += op;  /* op is negative */
        }
        s->sempid = 1;  /* TODO: Get from process */
    }

    set->ds.sem_otime = exo_get_time_ns() / 1000000000ULL;
    return 0;
}

/**
 * Semaphore control
 */
long linux_sys_semctl(int semid, int semnum, int cmd, unsigned long arg)
{
    struct sem_set *set = sem_find_by_id(semid);
    if (!set && cmd != IPC_INFO && cmd != SEM_INFO) {
        return -LINUX_EINVAL;
    }

    switch (cmd) {
    case IPC_STAT:
    case SEM_STAT:
        {
            struct semid_ds *buf = (struct semid_ds *)arg;
            if (!buf) return -LINUX_EFAULT;
            *buf = set->ds;
            return 0;
        }

    case IPC_SET:
        {
            struct semid_ds *buf = (struct semid_ds *)arg;
            if (!buf) return -LINUX_EFAULT;
            set->ds.sem_perm.uid = buf->sem_perm.uid;
            set->ds.sem_perm.gid = buf->sem_perm.gid;
            set->ds.sem_perm.mode = buf->sem_perm.mode & 0777;
            set->ds.sem_ctime = exo_get_time_ns() / 1000000000ULL;
            return 0;
        }

    case IPC_RMID:
        exo_free_pages(set->sems, (set->ds.sem_nsems * sizeof(struct sem) + 4095) / 4096);
        set->in_use = false;
        return 0;

    case GETVAL:
        if (semnum >= (int)set->ds.sem_nsems) return -LINUX_EINVAL;
        return set->sems[semnum].semval;

    case SETVAL:
        if (semnum >= (int)set->ds.sem_nsems) return -LINUX_EINVAL;
        if ((int)arg < 0 || (int)arg > SEMVMX) return -LINUX_ERANGE;
        set->sems[semnum].semval = (int16_t)arg;
        set->ds.sem_ctime = exo_get_time_ns() / 1000000000ULL;
        return 0;

    case GETPID:
        if (semnum >= (int)set->ds.sem_nsems) return -LINUX_EINVAL;
        return set->sems[semnum].sempid;

    case GETNCNT:
        if (semnum >= (int)set->ds.sem_nsems) return -LINUX_EINVAL;
        return set->sems[semnum].semncnt;

    case GETZCNT:
        if (semnum >= (int)set->ds.sem_nsems) return -LINUX_EINVAL;
        return set->sems[semnum].semzcnt;

    case GETALL:
        {
            uint16_t *array = (uint16_t *)arg;
            if (!array) return -LINUX_EFAULT;
            for (size_t i = 0; i < set->ds.sem_nsems; i++) {
                array[i] = set->sems[i].semval;
            }
            return 0;
        }

    case SETALL:
        {
            uint16_t *array = (uint16_t *)arg;
            if (!array) return -LINUX_EFAULT;
            for (size_t i = 0; i < set->ds.sem_nsems; i++) {
                set->sems[i].semval = array[i];
            }
            set->ds.sem_ctime = exo_get_time_ns() / 1000000000ULL;
            return 0;
        }

    default:
        return -LINUX_EINVAL;
    }
}

/*============================================================================
 * Message Queue Implementation
 *============================================================================*/

/**
 * Message queue descriptor
 */
struct msqid_ds {
    struct ipc_perm msg_perm;   /* Permissions */
    uint64_t    msg_stime;      /* Last msgsnd time */
    uint64_t    msg_rtime;      /* Last msgrcv time */
    uint64_t    msg_ctime;      /* Creation/change time */
    uint64_t    msg_cbytes;     /* Current bytes in queue */
    uint64_t    msg_qnum;       /* Number of messages */
    uint64_t    msg_qbytes;     /* Max bytes allowed */
    int32_t     msg_lspid;      /* Last msgsnd PID */
    int32_t     msg_lrpid;      /* Last msgrcv PID */
    uint64_t    _pad1;
    uint64_t    _pad2;
};

/**
 * Message buffer structure (for user)
 */
struct msgbuf {
    long mtype;                 /* Message type (> 0) */
    char mtext[1];              /* Message data */
};

/**
 * Internal message structure
 */
struct msg {
    struct msg *next;           /* Next message in queue */
    long mtype;                 /* Message type */
    size_t msize;               /* Message size */
    char data[];                /* Message data */
};

/**
 * Message queue
 */
struct msg_queue {
    int id;                     /* Queue ID */
    uint32_t key;               /* Key */
    struct msqid_ds ds;         /* Descriptor */
    struct msg *first;          /* First message */
    struct msg *last;           /* Last message */
    bool in_use;
};

/* Message queue table */
#define MSG_MAX_QUEUES 256
static struct msg_queue msg_queues[MSG_MAX_QUEUES];
static int msg_next_id = 1;

/**
 * Find message queue by key
 */
static struct msg_queue *msg_find_by_key(uint32_t key)
{
    if (key == IPC_PRIVATE) {
        return NULL;
    }

    for (int i = 0; i < MSG_MAX_QUEUES; i++) {
        if (msg_queues[i].in_use && msg_queues[i].key == key) {
            return &msg_queues[i];
        }
    }
    return NULL;
}

/**
 * Find message queue by ID
 */
static struct msg_queue *msg_find_by_id(int msqid)
{
    for (int i = 0; i < MSG_MAX_QUEUES; i++) {
        if (msg_queues[i].in_use && msg_queues[i].id == msqid) {
            return &msg_queues[i];
        }
    }
    return NULL;
}

/**
 * Allocate message queue
 */
static struct msg_queue *msg_alloc(void)
{
    for (int i = 0; i < MSG_MAX_QUEUES; i++) {
        if (!msg_queues[i].in_use) {
            msg_queues[i].in_use = true;
            msg_queues[i].id = msg_next_id++;
            return &msg_queues[i];
        }
    }
    return NULL;
}

/**
 * Get or create message queue
 */
long linux_sys_msgget(uint32_t key, int msgflg)
{
    struct msg_queue *q = msg_find_by_key(key);

    if (q) {
        if ((msgflg & IPC_CREAT) && (msgflg & IPC_EXCL)) {
            return -LINUX_EEXIST;
        }
        return q->id;
    }

    if (!(msgflg & IPC_CREAT) && key != IPC_PRIVATE) {
        return -LINUX_ENOENT;
    }

    q = msg_alloc();
    if (!q) {
        return -LINUX_ENOSPC;
    }

    /* Initialize */
    q->key = key;
    q->first = NULL;
    q->last = NULL;
    q->ds.msg_perm.key = key;
    q->ds.msg_perm.mode = msgflg & 0777;
    q->ds.msg_cbytes = 0;
    q->ds.msg_qnum = 0;
    q->ds.msg_qbytes = MSGMNB;
    q->ds.msg_lspid = 0;
    q->ds.msg_lrpid = 0;
    q->ds.msg_stime = 0;
    q->ds.msg_rtime = 0;
    q->ds.msg_ctime = exo_get_time_ns() / 1000000000ULL;

    return q->id;
}

/**
 * Send message to queue
 */
long linux_sys_msgsnd(int msqid, const void *msgp, size_t msgsz, int msgflg)
{
    struct msg_queue *q = msg_find_by_id(msqid);
    if (!q) {
        return -LINUX_EINVAL;
    }

    const struct msgbuf *buf = (const struct msgbuf *)msgp;
    if (!buf || buf->mtype <= 0) {
        return -LINUX_EINVAL;
    }

    if (msgsz > MSGMAX) {
        return -LINUX_EINVAL;
    }

    /* Check queue space */
    while (q->ds.msg_cbytes + msgsz > q->ds.msg_qbytes) {
        if (msgflg & IPC_NOWAIT) {
            return -LINUX_EAGAIN;
        }
        extern int exo_thread_yield(void);
        exo_thread_yield();
    }

    /* Allocate message */
    size_t total_size = sizeof(struct msg) + msgsz;
    size_t pages = (total_size + 4095) / 4096;
    struct msg *m = (struct msg *)exo_alloc_pages(pages);
    if (!m) {
        return -LINUX_ENOMEM;
    }

    /* Copy message */
    m->next = NULL;
    m->mtype = buf->mtype;
    m->msize = msgsz;
    for (size_t i = 0; i < msgsz; i++) {
        m->data[i] = buf->mtext[i];
    }

    /* Add to queue */
    if (q->last) {
        q->last->next = m;
    } else {
        q->first = m;
    }
    q->last = m;

    q->ds.msg_qnum++;
    q->ds.msg_cbytes += msgsz;
    q->ds.msg_lspid = 1;  /* TODO: Get from process */
    q->ds.msg_stime = exo_get_time_ns() / 1000000000ULL;

    return 0;
}

/**
 * Receive message from queue
 */
long linux_sys_msgrcv(int msqid, void *msgp, size_t msgsz, long msgtyp, int msgflg)
{
    struct msg_queue *q = msg_find_by_id(msqid);
    if (!q) {
        return -LINUX_EINVAL;
    }

    struct msgbuf *buf = (struct msgbuf *)msgp;
    if (!buf) {
        return -LINUX_EFAULT;
    }

    struct msg *m = NULL;
    struct msg **prev = &q->first;

    /* Find matching message */
    while (1) {
        for (struct msg *curr = q->first; curr; prev = &curr->next, curr = curr->next) {
            bool match = false;

            if (msgtyp == 0) {
                /* Any message */
                match = true;
            } else if (msgtyp > 0) {
                /* Specific type */
                if (msgflg & MSG_EXCEPT) {
                    match = (curr->mtype != msgtyp);
                } else {
                    match = (curr->mtype == msgtyp);
                }
            } else {
                /* First with type <= |msgtyp| */
                match = (curr->mtype <= -msgtyp);
            }

            if (match) {
                m = curr;
                break;
            }
        }

        if (m) break;

        if (msgflg & IPC_NOWAIT) {
            return -LINUX_ENOMSG;
        }

        extern int exo_thread_yield(void);
        exo_thread_yield();
    }

    /* Check size */
    size_t copy_size = m->msize;
    if (copy_size > msgsz) {
        if (!(msgflg & MSG_NOERROR)) {
            return -LINUX_E2BIG;
        }
        copy_size = msgsz;
    }

    /* Copy message */
    buf->mtype = m->mtype;
    for (size_t i = 0; i < copy_size; i++) {
        buf->mtext[i] = m->data[i];
    }

    /* Remove from queue (unless MSG_COPY) */
    if (!(msgflg & MSG_COPY)) {
        *prev = m->next;
        if (q->last == m) {
            q->last = (prev == &q->first) ? NULL :
                      (struct msg *)((char *)prev - offsetof(struct msg, next));
        }
        q->ds.msg_qnum--;
        q->ds.msg_cbytes -= m->msize;

        size_t pages = (sizeof(struct msg) + m->msize + 4095) / 4096;
        exo_free_pages(m, pages);
    }

    q->ds.msg_lrpid = 1;  /* TODO: Get from process */
    q->ds.msg_rtime = exo_get_time_ns() / 1000000000ULL;

    return copy_size;
}

/**
 * Message queue control
 */
long linux_sys_msgctl(int msqid, int cmd, struct msqid_ds *buf)
{
    struct msg_queue *q = msg_find_by_id(msqid);
    if (!q && cmd != IPC_INFO && cmd != MSG_INFO) {
        return -LINUX_EINVAL;
    }

    switch (cmd) {
    case IPC_STAT:
    case MSG_STAT:
        if (!buf) return -LINUX_EFAULT;
        *buf = q->ds;
        return 0;

    case IPC_SET:
        if (!buf) return -LINUX_EFAULT;
        q->ds.msg_perm.uid = buf->msg_perm.uid;
        q->ds.msg_perm.gid = buf->msg_perm.gid;
        q->ds.msg_perm.mode = buf->msg_perm.mode & 0777;
        q->ds.msg_qbytes = buf->msg_qbytes;
        q->ds.msg_ctime = exo_get_time_ns() / 1000000000ULL;
        return 0;

    case IPC_RMID:
        /* Free all messages */
        while (q->first) {
            struct msg *m = q->first;
            q->first = m->next;
            size_t pages = (sizeof(struct msg) + m->msize + 4095) / 4096;
            exo_free_pages(m, pages);
        }
        q->in_use = false;
        return 0;

    case IPC_INFO:
    case MSG_INFO:
        return 0;

    default:
        return -LINUX_EINVAL;
    }
}

/*============================================================================
 * Debugging Interface
 *============================================================================*/

/**
 * Get IPC statistics
 */
int linux_get_ipc_stats(int *shm_count, int *sem_count, int *msg_count)
{
    int shm = 0, sem = 0, msg = 0;

    for (int i = 0; i < SHM_MAX_SEGMENTS; i++) {
        if (shm_segments[i].in_use) shm++;
    }
    for (int i = 0; i < SEM_MAX_SETS; i++) {
        if (sem_sets[i].in_use) sem++;
    }
    for (int i = 0; i < MSG_MAX_QUEUES; i++) {
        if (msg_queues[i].in_use) msg++;
    }

    if (shm_count) *shm_count = shm;
    if (sem_count) *sem_count = sem;
    if (msg_count) *msg_count = msg;

    return 0;
}

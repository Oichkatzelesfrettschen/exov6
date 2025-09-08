/*
 * libos_framework.c - Library Operating System Framework
 * 
 * Implements OS abstractions and policies on top of exokernel primitives.
 * Each LibOS can implement its own OS personality (UNIX, Plan 9, etc.)
 * while sharing the same exokernel.
 * 
 * Key principles:
 * - LibOS implements ALL policy decisions
 * - Direct hardware access through secure bindings
 * - Application-specific optimizations
 * - Untrusted but privileged execution
 */

#include <stdint.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdatomic.h>
#include <stdalign.h>
#include <string.h>

#include "types.h"
#include "libos.h"
#include "exokernel.h"
#include "capability.h"

/* ============================================================================
 * LibOS Types - Different OS Personalities
 * ============================================================================ */

typedef enum {
    LIBOS_TYPE_POSIX = 0,      /* POSIX/UNIX personality */
    LIBOS_TYPE_PLAN9,          /* Plan 9 personality */
    LIBOS_TYPE_LISP,           /* Lisp Machine personality */
    LIBOS_TYPE_REALTIME,       /* Real-time OS personality */
    LIBOS_TYPE_DATABASE,       /* Database OS (like DBOS) */
    LIBOS_TYPE_NETWORK,        /* Network appliance OS */
    LIBOS_TYPE_CONTAINER,      /* Container runtime */
    LIBOS_TYPE_UNIKERNEL,      /* Single-application kernel */
    LIBOS_TYPE_CUSTOM          /* Custom application-specific */
} libos_type_t;

/* ============================================================================
 * LibOS Core Structure - OS Implementation
 * ============================================================================ */

typedef struct libos_core {
    _Alignas(64) struct {
        /* Identity */
        uint64_t libos_id;
        libos_type_t type;
        char name[32];
        
        /* Exokernel interface */
        uint64_t exo_binding_id;        /* Binding to exokernel */
        uint64_t root_capability;       /* Root capability */
        
        /* Virtual memory management */
        struct {
            void *page_table;            /* Hardware page table */
            _Atomic(uint64_t) brk;       /* Program break */
            _Atomic(uint64_t) mmap_base; /* mmap region base */
            
            /* Page fault handler */
            int (*page_fault_handler)(uint64_t addr, uint32_t error);
            
            /* Custom memory allocator */
            void* (*malloc)(size_t size);
            void (*free)(void *ptr);
            
            /* Page replacement policy */
            void (*page_evict)(uint64_t vpn);
            void (*page_load)(uint64_t vpn);
        } memory;
        
        /* Process/Thread management */
        struct {
            /* Process table */
            void *process_table;
            _Atomic(uint32_t) next_pid;
            
            /* Scheduler implementation */
            void (*schedule)(void);
            void (*yield)(void);
            void (*block)(uint64_t reason);
            void (*unblock)(uint64_t pid);
            
            /* Thread support */
            int (*thread_create)(void *(*func)(void*), void *arg);
            void (*thread_exit)(void *result);
            int (*thread_join)(uint64_t tid, void **result);
        } process;
        
        /* File system implementation */
        struct {
            /* VFS operations */
            int (*open)(const char *path, int flags, mode_t mode);
            int (*close)(int fd);
            ssize_t (*read)(int fd, void *buf, size_t count);
            ssize_t (*write)(int fd, const void *buf, size_t count);
            off_t (*lseek)(int fd, off_t offset, int whence);
            
            /* File system specific */
            void *fs_private;
            
            /* Buffer cache */
            void *buffer_cache;
            size_t cache_size;
        } filesystem;
        
        /* Network stack */
        struct {
            /* Protocol handlers */
            int (*socket)(int domain, int type, int protocol);
            int (*bind)(int sockfd, const void *addr, socklen_t addrlen);
            int (*listen)(int sockfd, int backlog);
            int (*accept)(int sockfd, void *addr, socklen_t *addrlen);
            int (*connect)(int sockfd, const void *addr, socklen_t addrlen);
            
            /* Network stack private data */
            void *net_private;
        } network;
        
        /* IPC implementation */
        struct {
            /* IPC operations */
            int (*pipe)(int pipefd[2]);
            int (*msgget)(key_t key, int msgflg);
            int (*msgsnd)(int msqid, const void *msgp, size_t msgsz, int msgflg);
            int (*msgrcv)(int msqid, void *msgp, size_t msgsz, long msgtyp, int msgflg);
            
            /* Shared memory */
            int (*shmget)(key_t key, size_t size, int shmflg);
            void* (*shmat)(int shmid, const void *shmaddr, int shmflg);
            int (*shmdt)(const void *shmaddr);
        } ipc;
        
        /* System call table */
        int (*syscall_table[512])(uint64_t, uint64_t, uint64_t, 
                                  uint64_t, uint64_t, uint64_t);
        
        /* Performance optimization */
        struct {
            /* Downloaded code cache */
            void *code_cache[32];
            
            /* JIT compiler */
            void* (*jit_compile)(const void *code, size_t size);
            
            /* Profiling data */
            _Atomic(uint64_t) hot_paths[1024];
            _Atomic(uint64_t) cache_misses;
            _Atomic(uint64_t) branch_mispredicts;
        } optimization;
        
        /* Statistics */
        _Atomic(uint64_t) syscalls_handled;
        _Atomic(uint64_t) page_faults_handled;
        _Atomic(uint64_t) context_switches;
        _Atomic(uint64_t) cpu_cycles_used;
    } data;
} libos_core_t;

/* ============================================================================
 * POSIX LibOS Implementation
 * ============================================================================ */

/* POSIX process structure */
typedef struct posix_process {
    uint32_t pid;
    uint32_t ppid;
    uid_t uid;
    gid_t gid;
    
    /* File descriptors */
    int fd_table[1024];
    
    /* Signal handling */
    void (*signal_handlers[64])(int);
    sigset_t signal_mask;
    
    /* Memory map */
    struct vm_area {
        uint64_t start;
        uint64_t end;
        uint32_t prot;
        uint32_t flags;
        struct vm_area *next;
    } *vm_areas;
    
    /* Scheduling */
    uint32_t priority;
    uint64_t timeslice;
    _Atomic(uint32_t) state;  /* RUNNING, READY, BLOCKED, etc. */
} posix_process_t;

/* POSIX scheduler implementation */
static void posix_schedule(libos_core_t *libos) {
    /* Implement Completely Fair Scheduler (CFS) */
    static _Atomic(uint64_t) min_vruntime = 0;
    
    posix_process_t *current = NULL;
    posix_process_t *next = NULL;
    uint64_t min_runtime = UINT64_MAX;
    
    /* Find process with minimum virtual runtime */
    /* This would iterate through process table */
    
    if (next && next != current) {
        /* Context switch via exokernel */
        exo_switch_context(current, next);
    }
}

/* POSIX page fault handler */
static int posix_page_fault(libos_core_t *libos, uint64_t addr, uint32_t error) {
    /* Check if address is valid */
    posix_process_t *proc = posix_get_current_process();
    
    struct vm_area *vma = proc->vm_areas;
    while (vma) {
        if (addr >= vma->start && addr < vma->end) {
            /* Valid address, allocate page */
            uint64_t page = exo_allocate_page();
            if (page == 0) {
                /* Out of memory, try to evict */
                libos->data.memory.page_evict(addr >> 12);
                page = exo_allocate_page();
                if (page == 0) {
                    return -ENOMEM;
                }
            }
            
            /* Map page */
            exo_map_page(addr & ~0xFFF, page, vma->prot);
            return 0;
        }
        vma = vma->next;
    }
    
    /* Segmentation fault */
    return -EFAULT;
}

/* POSIX malloc implementation */
static void* posix_malloc(libos_core_t *libos, size_t size) {
    /* Doug Lea's malloc or jemalloc implementation */
    /* For now, simple bump allocator */
    
    static _Atomic(uint64_t) heap_ptr = 0x100000000;  /* 4GB base */
    
    uint64_t addr = atomic_fetch_add_explicit(&heap_ptr, 
                                              (size + 15) & ~15,
                                              memory_order_relaxed);
    
    /* Ensure pages are mapped */
    for (uint64_t page = addr & ~0xFFF; 
         page < addr + size; 
         page += 4096) {
        if (!exo_is_mapped(page)) {
            uint64_t phys = exo_allocate_page();
            exo_map_page(page, phys, PROT_READ | PROT_WRITE);
        }
    }
    
    return (void*)addr;
}

/* POSIX system call: open */
static int posix_sys_open(libos_core_t *libos, const char *pathname, 
                         int flags, mode_t mode) {
    posix_process_t *proc = posix_get_current_process();
    
    /* Find free file descriptor */
    int fd = -1;
    for (int i = 3; i < 1024; i++) {  /* Skip 0,1,2 (stdin/out/err) */
        if (proc->fd_table[i] == -1) {
            fd = i;
            break;
        }
    }
    
    if (fd < 0) {
        return -EMFILE;
    }
    
    /* Call file system implementation */
    int file_handle = libos->data.filesystem.open(pathname, flags, mode);
    if (file_handle < 0) {
        return file_handle;
    }
    
    proc->fd_table[fd] = file_handle;
    return fd;
}

/* ============================================================================
 * Plan 9 LibOS Implementation
 * ============================================================================ */

/* Plan 9 namespace */
typedef struct p9_namespace {
    struct p9_mount {
        char *path;
        char *device;
        int flags;
        struct p9_mount *next;
    } *mounts;
    
    /* 9P connections */
    struct p9_conn {
        int fd;
        char *addr;
        struct p9_conn *next;
    } *connections;
} p9_namespace_t;

/* Plan 9 everything-is-a-file approach */
static int p9_sys_open(libos_core_t *libos, const char *path, int flags) {
    /* In Plan 9, everything is accessed as a file */
    /* This includes processes, network connections, etc. */
    
    if (strncmp(path, "/proc/", 6) == 0) {
        /* Process file system */
        return p9_open_proc(path + 6, flags);
    } else if (strncmp(path, "/net/", 5) == 0) {
        /* Network file system */
        return p9_open_net(path + 5, flags);
    } else {
        /* Regular file */
        return p9_open_file(path, flags);
    }
}

/* ============================================================================
 * Real-Time LibOS Implementation
 * ============================================================================ */

/* Real-time task structure */
typedef struct rt_task {
    uint64_t wcet;          /* Worst-case execution time */
    uint64_t deadline;      /* Absolute deadline */
    uint64_t period;        /* Task period */
    uint32_t priority;      /* Static priority */
    
    void (*entry)(void*);   /* Task entry point */
    void *arg;              /* Task argument */
    
    _Atomic(uint64_t) next_release;
    _Atomic(bool) ready;
} rt_task_t;

/* EDF (Earliest Deadline First) scheduler */
static void rt_schedule(libos_core_t *libos) {
    rt_task_t *tasks = (rt_task_t*)libos->data.process.process_table;
    rt_task_t *next = NULL;
    uint64_t earliest_deadline = UINT64_MAX;
    
    /* Find task with earliest deadline */
    for (int i = 0; i < 256; i++) {
        if (atomic_load(&tasks[i].ready) &&
            tasks[i].deadline < earliest_deadline) {
            earliest_deadline = tasks[i].deadline;
            next = &tasks[i];
        }
    }
    
    if (next) {
        /* Switch to task with earliest deadline */
        exo_switch_to_task(next);
    }
}

/* ============================================================================
 * LibOS Creation and Management
 * ============================================================================ */

/**
 * libos_create - Create a new LibOS instance
 * @type: Type of LibOS (POSIX, Plan9, etc.)
 * @name: Name for this LibOS instance
 * @capability: Root capability
 * 
 * Returns: Pointer to LibOS or NULL on failure
 */
libos_core_t* libos_create(libos_type_t type, const char *name,
                           uint64_t capability) {
    /* Allocate LibOS structure */
    libos_core_t *libos = (libos_core_t*)exo_allocate_pages(
        sizeof(libos_core_t) / 4096 + 1);
    
    if (!libos) {
        return NULL;
    }
    
    /* Initialize common fields */
    libos->data.libos_id = exo_create_libos(name, capability);
    libos->data.type = type;
    strncpy(libos->data.name, name, 31);
    libos->data.root_capability = capability;
    
    /* Initialize based on type */
    switch (type) {
    case LIBOS_TYPE_POSIX:
        libos_init_posix(libos);
        break;
        
    case LIBOS_TYPE_PLAN9:
        libos_init_plan9(libos);
        break;
        
    case LIBOS_TYPE_REALTIME:
        libos_init_realtime(libos);
        break;
        
    case LIBOS_TYPE_DATABASE:
        libos_init_database(libos);
        break;
        
    default:
        libos_init_custom(libos);
        break;
    }
    
    /* Register with exokernel */
    exo_register_libos(libos->data.libos_id, libos);
    
    return libos;
}

/**
 * libos_init_posix - Initialize POSIX LibOS
 */
static void libos_init_posix(libos_core_t *libos) {
    /* Memory management */
    libos->data.memory.page_fault_handler = posix_page_fault;
    libos->data.memory.malloc = posix_malloc;
    libos->data.memory.free = posix_free;
    
    /* Process management */
    libos->data.process.schedule = posix_schedule;
    libos->data.process.yield = posix_yield;
    libos->data.process.thread_create = pthread_create;
    
    /* File system */
    libos->data.filesystem.open = posix_open;
    libos->data.filesystem.close = posix_close;
    libos->data.filesystem.read = posix_read;
    libos->data.filesystem.write = posix_write;
    
    /* Network */
    libos->data.network.socket = posix_socket;
    libos->data.network.bind = posix_bind;
    libos->data.network.connect = posix_connect;
    
    /* System calls */
    libos->data.syscall_table[SYS_open] = posix_sys_open;
    libos->data.syscall_table[SYS_close] = posix_sys_close;
    libos->data.syscall_table[SYS_read] = posix_sys_read;
    libos->data.syscall_table[SYS_write] = posix_sys_write;
    libos->data.syscall_table[SYS_fork] = posix_sys_fork;
    libos->data.syscall_table[SYS_exec] = posix_sys_exec;
    /* ... and so on for all POSIX syscalls */
}

/* ============================================================================
 * Application-Specific Optimization
 * ============================================================================ */

/**
 * libos_optimize - Perform application-specific optimization
 * @libos: LibOS to optimize
 * @hint: Optimization hint from application
 */
void libos_optimize(libos_core_t *libos, uint32_t hint) {
    switch (hint) {
    case OPTIMIZE_THROUGHPUT:
        /* Optimize for throughput */
        libos_optimize_throughput(libos);
        break;
        
    case OPTIMIZE_LATENCY:
        /* Optimize for latency */
        libos_optimize_latency(libos);
        break;
        
    case OPTIMIZE_MEMORY:
        /* Optimize for memory usage */
        libos_optimize_memory(libos);
        break;
        
    case OPTIMIZE_POWER:
        /* Optimize for power consumption */
        libos_optimize_power(libos);
        break;
    }
}

/**
 * libos_download_handler - Download optimized handler
 * @libos: LibOS instance
 * @syscall: System call to optimize
 * @code: Optimized code
 * @size: Code size
 */
int libos_download_handler(libos_core_t *libos, int syscall,
                          const void *code, size_t size) {
    /* Download code to exokernel */
    int slot = exo_download_code(libos->data.libos_id, code, size,
                                 libos->data.root_capability);
    
    if (slot >= 0) {
        /* Replace syscall handler with downloaded code */
        libos->data.optimization.code_cache[syscall % 32] = (void*)slot;
        
        /* Update syscall table to use optimized version */
        libos->data.syscall_table[syscall] = libos_optimized_syscall;
    }
    
    return slot;
}

/* ============================================================================
 * LibOS System Call Dispatcher
 * ============================================================================ */

/**
 * libos_syscall - Main system call entry point
 * @libos: LibOS handling the syscall
 * @nr: System call number
 * @args: System call arguments
 */
int64_t libos_syscall(libos_core_t *libos, uint64_t nr, uint64_t args[6]) {
    /* Update statistics */
    atomic_fetch_add_explicit(&libos->data.syscalls_handled, 1,
                             memory_order_relaxed);
    
    /* Bounds check */
    if (nr >= 512 || !libos->data.syscall_table[nr]) {
        return -ENOSYS;
    }
    
    /* Check for optimized version */
    int cache_slot = nr % 32;
    if (libos->data.optimization.code_cache[cache_slot]) {
        /* Execute downloaded optimized code */
        return exo_execute_downloaded(libos->data.libos_id,
                                      (int)(intptr_t)libos->data.optimization.code_cache[cache_slot],
                                      args);
    }
    
    /* Call regular handler */
    return libos->data.syscall_table[nr](args[0], args[1], args[2],
                                         args[3], args[4], args[5]);
}

/* ============================================================================
 * LibOS Fault Handling
 * ============================================================================ */

/**
 * libos_fault_handler - Handle faults for LibOS
 * @libos: LibOS instance
 * @type: Fault type
 * @addr: Fault address
 * @error: Error code
 */
int libos_fault_handler(libos_core_t *libos, uint32_t type,
                       uint64_t addr, uint32_t error) {
    switch (type) {
    case FAULT_PAGE:
        /* Page fault */
        atomic_fetch_add_explicit(&libos->data.page_faults_handled, 1,
                                 memory_order_relaxed);
        return libos->data.memory.page_fault_handler(addr, error);
        
    case FAULT_PROTECTION:
        /* Protection fault */
        return libos_protection_fault(libos, addr, error);
        
    case FAULT_ALIGNMENT:
        /* Alignment fault */
        return libos_alignment_fault(libos, addr, error);
        
    default:
        return -EFAULT;
    }
}

/* ============================================================================
 * LibOS Performance Monitoring
 * ============================================================================ */

/**
 * libos_get_stats - Get LibOS statistics
 * @libos: LibOS instance
 * @stats: Output statistics structure
 */
void libos_get_stats(libos_core_t *libos, struct libos_stats *stats) {
    stats->syscalls = atomic_load(&libos->data.syscalls_handled);
    stats->page_faults = atomic_load(&libos->data.page_faults_handled);
    stats->context_switches = atomic_load(&libos->data.context_switches);
    stats->cpu_cycles = atomic_load(&libos->data.cpu_cycles_used);
    
    /* Get optimization stats */
    stats->cache_misses = atomic_load(&libos->data.optimization.cache_misses);
    stats->branch_mispredicts = atomic_load(&libos->data.optimization.branch_mispredicts);
    
    /* Calculate hot paths */
    stats->hot_path_count = 0;
    for (int i = 0; i < 1024; i++) {
        if (atomic_load(&libos->data.optimization.hot_paths[i]) > 1000) {
            stats->hot_path_count++;
        }
    }
}
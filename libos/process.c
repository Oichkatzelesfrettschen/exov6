/**
 * process.c - Advanced process management for FeuerBird LibOS
 * 
 * Implements POSIX-2024 process management with COW optimization,
 * capability preservation, and exokernel integration.
 */

#include <stdatomic.h> /* Added for atomic operations */
#include "types.h"
/* #include "defs.h" - REMOVED: Kernel dependency */
#include "param.h"
/* #include "memlayout.h" - REMOVED: Kernel dependency */
/* #include "mmu.h" - REMOVED: Kernel dependency */
#include <arch.h>
/* #include "proc.h" - REMOVED: Kernel dependency */
/* #include "spinlock.h" - REMOVED: Kernel dependency */
#include "libos/posix.h"
#include "exo.h"
#include "errno.h"
#include <signal.h>
#include <sys/wait.h>
#include <sys/resource.h>
#include <unistd.h>
#include <stdlib.h>  /* for malloc */
#include <string.h>  /* for memcpy */
#include "file_types.h"  /* for T_FILE */
#include "file.h"  /* for struct inode */
#include "elf.h" /* Added for ELF structures */

#ifndef PGSIZE
#define PGSIZE 4096
#endif

/* Internal FS declarations (stubbed in libfs_stubs.c) */
struct inode *idup(struct inode *ip);
struct inode *namei(const char *path);
void ilock(struct inode *ip);
void iunlockput(struct inode *ip);
int readi(struct inode *ip, char *dst, uint32_t off, size_t n);
void iput(struct inode *ip);

/* POSIX declarations that might be missing */
int nice(int inc);
pid_t getpgid(pid_t pid);

/* Local Spinlock Implementation for User Space */
typedef struct {
    _Atomic int locked;
} libos_spinlock_t;

static void libos_initlock(libos_spinlock_t *lk, char *name) {
    (void)name;
    atomic_init(&lk->locked, 0);
}

static void libos_acquire(libos_spinlock_t *lk) {
    int expected = 0;
    while (!atomic_compare_exchange_weak(&lk->locked, &expected, 1)) {
        expected = 0;
        // TODO: yield to scheduler
        __builtin_ia32_pause();
    }
}

static void libos_release(libos_spinlock_t *lk) {
    atomic_store(&lk->locked, 0);
}

static void ksleep(void *chan, libos_spinlock_t *lk) {
    // TODO: Implement user-space sleep/wait using futex or exokernel yield
    libos_release(lk);
    // exo_yield_to(sched_cap);
    libos_acquire(lk);
}

static void wakeup1(void *chan) {
    // TODO: Implement user-space wakeup
}

static void panic(const char *msg) {
    // write(2, msg, strlen(msg));
    abort();
}

/* Architecture specific structures (should be in arch.h but simplified here) */
struct context {
    uint64_t r15;
    uint64_t r14;
    uint64_t r13;
    uint64_t r12;
    uint64_t rbx;
    uint64_t rbp;
    uint64_t rip;
};

struct trapframe {
    uint64_t rax;
    // ... full definition needed for real context switch
};

// Forward declaration for process type
typedef struct process process_t;

// Forward declarations  
static int setup_cow_memory(process_t *child, process_t *parent);
static int setup_child_context(process_t *child, process_t *parent);
static int clear_user_memory(process_t *p);
static int load_segment(struct inode *ip, uint32_t off, uint32_t vaddr, uint32_t filesz, uint32_t memsz, uint32_t flags);
static uint32_t setup_stack(char **argv, char **envp, int *argc);
static int commit_exec(uint32_t entry, uint32_t sp, int argc);
static int remove_child(process_t *parent, process_t *child);
static int send_signal(process_t *p, int sig);
static int calculate_priority(int nice);
static int can_signal(process_t *src, process_t *dest);
static int kill_pgrp(pid_t pgid, int sig);
static int kill_all(int sig);
static int begin_exec(void);
static void abort_exec(void);
static void sched(void);
void free_process(process_t *p);

// Process table
#define MAX_PROCESSES 65536
#define PROCESS_HASH_SIZE 1024

// Process state
typedef enum {
    PROC_UNUSED,
    PROC_EMBRYO,
    PROC_RUNNABLE,
    PROC_RUNNING,
    PROC_SLEEPING,
    PROC_ZOMBIE,
    PROC_STOPPED
} proc_state_t;

struct namespace {
    _Atomic int ref;
    unsigned int pid_ns; // Simplified PID namespace ID
    unsigned int net_ns; // Simplified Network namespace ID
};

// Process structure with modern features
typedef struct process {
    // Basic info
    pid_t pid;
    struct namespace *ns;          // Namespace reference
    pid_t ppid;
    pid_t pgid;                    // Process group ID
    pid_t sid;                     // Session ID
    uid_t uid;
    uid_t euid;                    // Effective UID
    uid_t suid;                    // Saved UID
    gid_t gid;
    gid_t egid;                    // Effective GID
    gid_t sgid;                    // Saved GID
    gid_t *groups;                 // Supplementary groups
    int ngroups;
    
    // State
    proc_state_t state;
    int exit_status;
    int stop_signal;
    
    // Capabilities
    exo_cap proc_cap;              // Process capability
    exo_cap mem_cap;               // Memory capability
    exo_cap cpu_cap;               // CPU capability
    
    // Memory management
    void *pgdir;                   // Page directory
    size_t sz;                     // Memory size
    void *heap_start;
    void *heap_end;
    void *stack_top;
    
    // File descriptors
    struct file *ofile[NOFILE];
    struct inode *cwd;
    
    // Signals
    sigset_t sigmask;              // Signal mask
    sigset_t sigpending;           // Pending signals
    struct sigaction sighandlers[NSIG];
    stack_t sigaltstack;           // Alternate signal stack
    
    // Scheduling
    uint64_t utime;                // User CPU time
    uint64_t stime;                // System CPU time
    uint64_t cutime;               // Children user time
    uint64_t cstime;               // Children system time
    int nice;                      // Nice value
    int priority;                  // Dynamic priority
    
    // Process relationships
    struct process *parent;
    struct process *children;
    struct process *sibling;
    struct process *next_hash;
    
    // Synchronization
    libos_spinlock_t lock;
    void *wait_chan;               // Waiting channel
    
    // Thread support
    int is_thread;
    struct process *thread_group;
    
    // Resource limits
    struct rlimit rlimits[RLIM_NLIMITS];
    
    // Process name
    char name[16];
    
    // Context for switching
    struct context *context;
    struct trapframe *tf;
} process_t; // Added typedef name at end

// Global process table
static process_t proc_table[MAX_PROCESSES];
static process_t *proc_hash[PROCESS_HASH_SIZE];
static libos_spinlock_t proc_table_lock;
static pid_t next_pid = 1;

// Current process (per-CPU in SMP)
__thread process_t *current_proc = NULL;

// Initialize process subsystem
void
libos_process_init(void)
{
    libos_initlock(&proc_table_lock, "proctable");
    
    // Initialize process table
    for (int i = 0; i < MAX_PROCESSES; i++) {
        proc_table[i].state = PROC_UNUSED;
        libos_initlock(&proc_table[i].lock, "proc");
    }
    
    // Clear hash table
    memset(proc_hash, 0, sizeof(proc_hash));
}

// Hash function for PID
static inline uint32_t
pid_hash(pid_t pid)
{
    return pid % PROCESS_HASH_SIZE;
}

// Find process by PID
static process_t *
find_process(pid_t pid)
{
    uint32_t hash = pid_hash(pid);
    process_t *p;
    
    libos_acquire(&proc_table_lock);
    for (p = proc_hash[hash]; p != NULL; p = p->next_hash) {
        if (p->pid == pid) {
            libos_release(&proc_table_lock);
            return p;
        }
    }
    libos_release(&proc_table_lock);
    return NULL;
}

// Allocate new process
static process_t *
alloc_process(void)
{
    process_t *p;
    
    libos_acquire(&proc_table_lock);
    
    // Find unused slot
    for (int i = 0; i < MAX_PROCESSES; i++) {
        p = &proc_table[i];
        if (p->state == PROC_UNUSED) {
            p->state = PROC_EMBRYO;
            p->pid = next_pid++;
            
            // Add to hash table
            uint32_t hash = pid_hash(p->pid);
            p->next_hash = proc_hash[hash];
            proc_hash[hash] = p;
            
            libos_release(&proc_table_lock);
            
            // Initialize process
            p->ppid = current_proc ? current_proc->pid : 0;
            p->pgid = p->pid;  // New process group
            p->sid = current_proc ? current_proc->sid : p->pid;
            
            // Request capabilities from exokernel
            // Placeholder: exo_create_process_cap() not yet implemented
            // p->proc_cap = exo_create_process_cap();
            // p->mem_cap = exo_request_memory(PGSIZE * 16, EXO_PROT_READ | EXO_PROT_WRITE);  // Initial memory
            // p->cpu_cap = exo_request_cpu();
            
            // Initialize signals
            sigemptyset(&p->sigmask);
            sigemptyset(&p->sigpending);
            for (int i = 0; i < NSIG; i++) {
                p->sighandlers[i].sa_handler = SIG_DFL;
            }
            
            // Initialize resource limits
            for (int i = 0; i < RLIM_NLIMITS; i++) {
                p->rlimits[i].rlim_cur = RLIM_INFINITY;
                p->rlimits[i].rlim_max = RLIM_INFINITY;
            }
            
            return p;
        }
    }
    
    libos_release(&proc_table_lock);
    return NULL;
}

/* Stub functions to make it compile without full implementation */
static int setup_child_context(process_t *child, process_t *parent) { (void)child; (void)parent; return 0; }
static int clear_user_memory(process_t *p) { (void)p; return 0; }
static int load_segment(struct inode *ip, uint32_t off, uint32_t vaddr, uint32_t filesz, uint32_t memsz, uint32_t flags) { (void)ip; (void)off; (void)vaddr; (void)filesz; (void)memsz; (void)flags; return 0; }
static uint32_t setup_stack(char **argv, char **envp, int *argc) { (void)argv; (void)envp; (void)argc; return 0; }
static int commit_exec(uint32_t entry, uint32_t sp, int argc) { (void)entry; (void)sp; (void)argc; return 0; }
static int remove_child(process_t *parent, process_t *child) { (void)parent; (void)child; return 0; }
static int can_signal(process_t *src, process_t *dest) { (void)src; (void)dest; return 1; }
static int kill_pgrp(pid_t pgid, int sig) { (void)pgid; (void)sig; return 0; }
static int kill_all(int sig) { (void)sig; return 0; }
static int begin_exec(void) { return 0; }
static void abort_exec(void) { }
static void sched(void) { }
void free_process(process_t *p) { (void)p; }

// Mock exokernel functions
void exo_schedule_process(exo_cap p, exo_cap c) { (void)p; (void)c; }
exo_cap exo_create_cow_mapping(exo_cap m, size_t s) { (void)m; (void)s; exo_cap c = {0}; return c; }
void exo_mark_cow(exo_cap m, void* a, size_t s) { (void)m; (void)a; (void)s; }
void exo_release_capability(exo_cap c) { (void)c; }
void exo_set_scheduling_hint(exo_cap c, int p) { (void)c; (void)p; }

/**
 * fork - Create new process with COW optimization
 * 
 * Returns: Child PID in parent, 0 in child, -1 on error
 */
pid_t
libos_fork(void)
{
    process_t *child;
    
    if (!current_proc) {
        // We are in the root process/host environment
        return fork();
    }

    // Allocate new process
    child = alloc_process();
    if (child == NULL) {
        errno = EAGAIN;
        return -1;
    }
    
    // Copy process state
    libos_acquire(&current_proc->lock);
    
    child->uid = current_proc->uid;
    child->euid = current_proc->euid;
    child->suid = current_proc->suid;
    child->gid = current_proc->gid;
    child->egid = current_proc->egid;
    child->sgid = current_proc->sgid;
    
    // Copy supplementary groups
    if (current_proc->ngroups > 0) {
        child->groups = malloc(sizeof(gid_t) * current_proc->ngroups);
        memcpy(child->groups, current_proc->groups, 
               sizeof(gid_t) * current_proc->ngroups);
        child->ngroups = current_proc->ngroups;
    }
    
    // Copy signal state
    child->sigmask = current_proc->sigmask;
    memcpy(child->sighandlers, current_proc->sighandlers, 
           sizeof(child->sighandlers));
    
    // Copy resource limits
    memcpy(child->rlimits, current_proc->rlimits, sizeof(child->rlimits));
    
    // Copy name
    strncpy(child->name, current_proc->name, sizeof(child->name));
    
    // Copy file descriptors
    for (int i = 0; i < NOFILE; i++) {
        if (current_proc->ofile[i]) {
            child->ofile[i] = filedup(current_proc->ofile[i]);
        }
    }
    child->cwd = idup(current_proc->cwd);
    
    libos_release(&current_proc->lock);
    
    // COW (Copy-on-Write) memory setup
    if (setup_cow_memory(child, current_proc) < 0) {
        free_process(child);
        errno = ENOMEM;
        return -1;
    }
    
    // Set up child context
    if (setup_child_context(child, current_proc) < 0) {
        free_process(child);
        errno = EAGAIN;
        return -1;
    }
    
    // Add to parent's children list
    libos_acquire(&current_proc->lock);
    child->parent = current_proc;
    child->sibling = current_proc->children;
    current_proc->children = child;
    libos_release(&current_proc->lock);
    
    // Make child runnable
    libos_acquire(&child->lock);
    child->state = PROC_RUNNABLE;
    libos_release(&child->lock);
    
    // Schedule child
    exo_schedule_process(child->proc_cap, child->cpu_cap);
    
    // Return appropriately
    if (child == current_proc) {
        // We're in the child
        return 0;
    } else {
        // We're in the parent
        return child->pid;
    }
}

/**
 * Setup COW memory for child process
 */
static int
setup_cow_memory(process_t *child, process_t *parent)
{
    // Request COW capability from exokernel
    exo_cap cow_cap = exo_create_cow_mapping(parent->mem_cap, PGSIZE * 16);
    if (cow_cap.id == 0) {
        return -1;
    }
    
    child->mem_cap = cow_cap;
    child->sz = parent->sz;
    child->heap_start = parent->heap_start;
    child->heap_end = parent->heap_end;
    child->stack_top = parent->stack_top;
    
    // Mark parent pages as COW
    exo_mark_cow(parent->mem_cap, (void*)0x50000000, PGSIZE * 16);
    
    return 0;
}

/**
 * execve - Execute new program
 * 
 * @path: Program path
 * @argv: Arguments
 * @envp: Environment
 * 
 * Returns: -1 on error (doesn't return on success)
 */
int
libos_execve(const char *path, char *const argv[], char *const envp[])
{
    struct inode *ip;
    struct elfhdr elf;
    struct proghdr ph;
    int i, off;
    uint64_t argc, sp;
    
    if (!current_proc) {
        // Host fallback
        // return execve(path, argv, envp);
        return -1; // Not implemented in stub
    }

    // Begin execution transaction
    begin_exec();
    
    // Open executable
    if ((ip = namei(path)) == 0) {
        errno = ENOENT;
        abort_exec();
        return -1;
    }
    
    ilock(ip);
    
    // Check if it's a regular file
    if (ip->type != T_FILE) {
        iunlockput(ip);
        errno = EACCES;
        abort_exec();
        return -1;
    }
    
    // Read ELF header
    if (readi(ip, (char*)&elf, 0, sizeof(elf)) != sizeof(elf)) {
        iunlockput(ip);
        errno = ENOEXEC;
        abort_exec();
        return -1;
    }
    
    // Verify ELF magic
    if (elf.magic != ELF_MAGIC) {
        iunlockput(ip);
        errno = ENOEXEC;
        abort_exec();
        return -1;
    }
    
    // Clear old memory (preserve capabilities)
    clear_user_memory(current_proc);
    
    // Load program segments
    for (i = 0, off = elf.phoff; i < elf.phnum; i++, off += sizeof(ph)) {
        if (readi(ip, (char*)&ph, off, sizeof(ph)) != sizeof(ph)) {
            iunlockput(ip);
            errno = ENOEXEC;
            abort_exec();
            return -1;
        }
        
        if (ph.type != ELF_PROG_LOAD)
            continue;
        
        if (ph.memsz < ph.filesz) {
            iunlockput(ip);
            errno = ENOEXEC;
            abort_exec();
            return -1;
        }
        
        // Allocate and load segment
        if (load_segment(ip, ph.off, ph.vaddr, ph.filesz, ph.memsz, ph.flags) < 0) {
            iunlockput(ip);
            errno = ENOMEM;
            abort_exec();
            return -1;
        }
    }
    
    iunlockput(ip);
    
    // Set up new stack with arguments and environment
    sp = setup_stack((char**)argv, (char**)envp, (int*)&argc);
    if (sp == 0) {
        errno = E2BIG;
        abort_exec();
        return -1;
    }
    
    // Update process name
    if (argv && argv[0]) {
        char *name = strrchr(argv[0], '/');
        if (name)
            name++;
        else
            name = argv[0];
        strncpy(current_proc->name, name, sizeof(current_proc->name) - 1);
    }
    
    // Commit execution
    commit_exec(elf.entry, sp, argc);
    
    // This should not return
    return 0;
}

/**
 * wait - Wait for child process
 * 
 * @status: Status return pointer
 * 
 * Returns: PID of terminated child, -1 on error
 */
pid_t
libos_wait(int *status)
{
    return libos_waitpid(-1, status, 0);
}

/**
 * waitpid - Wait for specific child
 * 
 * @pid: PID to wait for (-1 for any)
 * @status: Status return pointer
 * @options: Wait options
 * 
 * Returns: PID of child, 0 if WNOHANG, -1 on error
 */
pid_t
libos_waitpid(pid_t pid, int *status, int options)
{
    process_t *p;
    int found_child = 0;
    
    if (!current_proc) return waitpid(pid, status, options);

    libos_acquire(&current_proc->lock);
    
    for (;;) {
        // Scan for zombie children
        for (p = current_proc->children; p != NULL; p = p->sibling) {
            // Check if this is the child we want
            if (pid > 0 && p->pid != pid)
                continue;
            if (pid == 0 && p->pgid != current_proc->pgid)
                continue;
            if (pid < -1 && p->pgid != -pid)
                continue;
            
            found_child = 1;
            
            libos_acquire(&p->lock);
            
            // Check for stopped child (WUNTRACED)
            if ((options & WUNTRACED) && p->state == PROC_STOPPED) {
                if (status)
                    *status = (p->stop_signal << 8) | 0x7f;
                pid_t ret = p->pid;
                libos_release(&p->lock);
                libos_release(&current_proc->lock);
                return ret;
            }
            
            // Check for continued child (WCONTINUED)
            if ((options & WCONTINUED) && p->state == PROC_RUNNABLE) {
                if (status)
                    *status = 0xffff;  // WIFCONTINUED
                pid_t ret = p->pid;
                libos_release(&p->lock);
                libos_release(&current_proc->lock);
                return ret;
            }
            
            // Check for zombie child
            if (p->state == PROC_ZOMBIE) {
                pid_t ret = p->pid;
                if (status)
                    *status = p->exit_status;
                
                // Add child times to parent
                current_proc->cutime += p->utime + p->cutime;
                current_proc->cstime += p->stime + p->cstime;
                
                // Remove from children list
                remove_child(current_proc, p);
                
                libos_release(&p->lock);
                
                // Free process resources
                free_process(p);
                
                libos_release(&current_proc->lock);
                return ret;
            }
            
            libos_release(&p->lock);
        }
        
        // No child found
        if (!found_child || (options & WNOHANG)) {
            libos_release(&current_proc->lock);
            if (!found_child) {
                errno = ECHILD;
                return -1;
            }
            return 0;  // WNOHANG
        }
        
        // Sleep waiting for child
        ksleep(current_proc, &current_proc->lock);
    }
}

/**
 * _exit - Terminate process
 * 
 * @status: Exit status
 */
void
libos_exit(int status)
{
    process_t *p;
    
    if (!current_proc) exit(status);

    // Close all open files
    for (int fd = 0; fd < NOFILE; fd++) {
        if (current_proc->ofile[fd]) {
            fileclose(current_proc->ofile[fd]);
            current_proc->ofile[fd] = 0;
        }
    }
    
    // Release current directory
    if (current_proc->cwd) {
        iput(current_proc->cwd);
        current_proc->cwd = 0;
    }
    
    libos_acquire(&current_proc->lock);
    
    // Set exit status
    current_proc->exit_status = (status & 0xff) << 8;
    
    // Reparent children to init
    libos_acquire(&proc_table_lock);
    process_t *init = find_process(1);
    if (init) {
        for (p = current_proc->children; p != NULL; p = p->sibling) {
            p->parent = init;
        }
        if (current_proc->children) {
            // Add children to init's list
            process_t *last = current_proc->children;
            while (last->sibling)
                last = last->sibling;
            last->sibling = init->children;
            init->children = current_proc->children;
            current_proc->children = NULL;
        }
    }
    libos_release(&proc_table_lock);
    
    // Wake up parent
    if (current_proc->parent)
        wakeup1(current_proc->parent);
    
    // Become zombie
    current_proc->state = PROC_ZOMBIE;
    
    // Release capabilities
    exo_release_capability(current_proc->cpu_cap);
    exo_release_capability(current_proc->mem_cap);
    
    // Never returns
    sched();
    panic("zombie exit");
}

/**
 * Process information getters
 */

pid_t
libos_getpid(void)
{
    return current_proc ? current_proc->pid : getpid();
}

pid_t
libos_getppid(void)
{
    return current_proc ? current_proc->ppid : getppid();
}

pid_t
libos_getpgid(pid_t pid)
{
    process_t *p;
    
    if (pid == 0) {
        return current_proc ? current_proc->pgid : getpgrp();
    }
    
    if (!current_proc) return getpgid(pid);

    p = find_process(pid);
    if (p == NULL) {
        errno = ESRCH;
        return -1;
    }
    
    return p->pgid;
}

int
libos_setpgid(pid_t pid, pid_t pgid)
{
    process_t *p;
    
    if (!current_proc) return setpgid(pid, pgid);

    if (pid == 0)
        pid = current_proc->pid;
    if (pgid == 0)
        pgid = pid;
    
    p = find_process(pid);
    if (p == NULL) {
        errno = ESRCH;
        return -1;
    }
    
    // Check permissions
    if (p != current_proc && p->parent != current_proc) {
        errno = EPERM;
        return -1;
    }
    
    // Check if process has already exec'd
    if (p->state != PROC_EMBRYO && p != current_proc) {
        errno = EACCES;
        return -1;
    }
    
    libos_acquire(&p->lock);
    p->pgid = pgid;
    libos_release(&p->lock);
    
    return 0;
}

pid_t
libos_getsid(pid_t pid)
{
    process_t *p;
    
    if (!current_proc) return getsid(pid);

    if (pid == 0) {
        return current_proc->sid;
    }
    
    p = find_process(pid);
    if (p == NULL) {
        errno = ESRCH;
        return -1;
    }
    
    return p->sid;
}

pid_t
libos_setsid(void)
{
    if (!current_proc) return setsid();

    // Check if already a process group leader
    if (current_proc->pid == current_proc->pgid) {
        errno = EPERM;
        return -1;
    }
    
    libos_acquire(&current_proc->lock);
    current_proc->sid = current_proc->pid;
    current_proc->pgid = current_proc->pid;
    libos_release(&current_proc->lock);
    
    return current_proc->sid;
}

/**
 * nice - Change process priority
 * 
 * @inc: Priority increment
 * 
 * Returns: New nice value, -1 on error
 */
int
libos_nice(int inc)
{
    if (!current_proc) return nice(inc);

    int old_nice = current_proc->nice;
    int new_nice = old_nice + inc;
    
    // Clamp to valid range [-20, 19]
    if (new_nice < -20)
        new_nice = -20;
    if (new_nice > 19)
        new_nice = 19;
    
    // Check permission for priority increase
    if (new_nice < old_nice && current_proc->euid != 0) {
        errno = EPERM;
        return -1;
    }
    
    libos_acquire(&current_proc->lock);
    current_proc->nice = new_nice;
    current_proc->priority = calculate_priority(new_nice);
    libos_release(&current_proc->lock);
    
    // Update exokernel scheduling hint
    exo_set_scheduling_hint(current_proc->cpu_cap, current_proc->priority);
    
    return new_nice;
}

/**
 * kill - Send signal to process
 * 
 * @pid: Target PID
 * @sig: Signal number
 * 
 * Returns: 0 on success, -1 on error
 */
int
libos_kill(pid_t pid, int sig)
{
    process_t *p;
    
    if (!current_proc) return kill(pid, sig);

    // Validate signal
    if (sig < 0 || sig >= NSIG) {
        errno = EINVAL;
        return -1;
    }
    
    // Special cases for pid
    if (pid > 0) {
        // Send to specific process
        p = find_process(pid);
        if (p == NULL) {
            errno = ESRCH;
            return -1;
        }
        return send_signal(p, sig);
    } else if (pid == 0) {
        // Send to process group
        return kill_pgrp(current_proc->pgid, sig);
    } else if (pid == -1) {
        // Send to all processes (except init)
        return kill_all(sig);
    } else {
        // Send to process group -pid
        return kill_pgrp(-pid, sig);
    }
}

// Helper functions
static int
send_signal(process_t *p, int sig)
{
    // Check permission
    if (!can_signal(current_proc, p)) {
        errno = EPERM;
        return -1;
    }
    
    libos_acquire(&p->lock);
    
    // Add to pending signals
    sigaddset(&p->sigpending, sig);
    
    // Wake up if sleeping
    if (p->state == PROC_SLEEPING) {
        p->state = PROC_RUNNABLE;
    }
    
    libos_release(&p->lock);
    
    return 0;
}

static int
calculate_priority(int nice)
{
    // Convert nice value to priority
    // Lower nice = higher priority
    return 120 - nice;
}
int libos_unshare(int flags) {
    if (!current_proc) return -1;

    struct namespace *new_ns = malloc(sizeof(struct namespace));
    if (!new_ns) {
        errno = ENOMEM;
        return -1;
    }
    atomic_init(&new_ns->ref, 1);

    // Default to inheriting
    if (current_proc->ns) {
        new_ns->pid_ns = current_proc->ns->pid_ns;
        new_ns->net_ns = current_proc->ns->net_ns;
    } else {
        new_ns->pid_ns = 0;
        new_ns->net_ns = 0;
    }

    // CLONE_NEWPID = 0x20000000
    if (flags & 0x20000000) {
        new_ns->pid_ns = (unsigned int)current_proc->pid;
    }
    // CLONE_NEWNET = 0x40000000
    if (flags & 0x40000000) {
        new_ns->net_ns = (unsigned int)current_proc->pid;
    }

    // Atomic swap (simplified, no locking for now as per granular plan)
    struct namespace *old_ns = current_proc->ns;
    current_proc->ns = new_ns;

    if (old_ns) {
         int r = atomic_fetch_sub(&old_ns->ref, 1);
         if (r == 1) free(old_ns);
    }

    return 0;
}

int libos_setns(int fd, int nstype) {
    (void)fd; (void)nstype;
    errno = EINVAL;
    return -1;
}

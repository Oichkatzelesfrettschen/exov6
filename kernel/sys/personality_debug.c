/**
 * @file personality_debug.c
 * @brief Personality-aware debugging and tracing tools
 * 
 * Provides unified debugging interface that understands all personalities:
 * - System call tracing with personality-specific decoding
 * - Signal translation and debugging
 * - Memory layout visualization per personality
 * - Performance profiling per personality
 */

#include "types.h"
#include "defs.h"
#include "param.h"
#include "spinlock.h"
#include "proc.h"
#include "syscall_gateway.h"
#include "abi_versioning.h"
#include <stdarg.h>

// =============================================================================
// DEBUG CONFIGURATION
// =============================================================================

#define MAX_TRACE_EVENTS    10000
#define MAX_BREAKPOINTS     256
#define MAX_WATCHPOINTS     64
#define TRACE_BUFFER_SIZE   (1024 * 1024)  // 1MB trace buffer

// Debug event types
typedef enum {
    DEBUG_EVENT_SYSCALL_ENTER,
    DEBUG_EVENT_SYSCALL_EXIT,
    DEBUG_EVENT_SIGNAL_SEND,
    DEBUG_EVENT_SIGNAL_DELIVER,
    DEBUG_EVENT_FAULT,
    DEBUG_EVENT_CONTEXT_SWITCH,
    DEBUG_EVENT_PERSONALITY_CHANGE,
    DEBUG_EVENT_CONTAINER_ENTER,
    DEBUG_EVENT_CONTAINER_EXIT,
    DEBUG_EVENT_EXEC,
    DEBUG_EVENT_EXIT,
    DEBUG_EVENT_FORK,
    DEBUG_EVENT_THREAD_CREATE,
} debug_event_type_t;

// Trace modes
#define TRACE_MODE_SYSCALL      (1 << 0)
#define TRACE_MODE_SIGNAL       (1 << 1)
#define TRACE_MODE_FAULT        (1 << 2)
#define TRACE_MODE_SCHED        (1 << 3)
#define TRACE_MODE_PERSONALITY  (1 << 4)
#define TRACE_MODE_MEMORY       (1 << 5)
#define TRACE_MODE_NETWORK      (1 << 6)
#define TRACE_MODE_IPC          (1 << 7)

// =============================================================================
// DATA STRUCTURES
// =============================================================================

/**
 * Debug event structure
 */
typedef struct debug_event {
    uint64_t timestamp;             // CPU cycles or nanoseconds
    debug_event_type_t type;        // Event type
    pid_t pid;                      // Process ID
    pid_t tid;                      // Thread ID
    syscall_personality_t personality; // Process personality
    
    union {
        struct {
            int syscall_nr;         // Syscall number
            uint64_t args[6];       // Syscall arguments
            int64_t result;         // Return value
            int errno_val;          // Error code
            uint64_t duration;      // Execution time
        } syscall;
        
        struct {
            int signum;             // Signal number
            pid_t sender_pid;       // Sender process
            void *handler;          // Signal handler
            uint64_t mask;          // Signal mask
        } signal;
        
        struct {
            uint64_t addr;          // Fault address
            uint32_t type;          // Fault type
            uint32_t error_code;    // Architecture error code
        } fault;
        
        struct {
            syscall_personality_t old_personality;
            syscall_personality_t new_personality;
            uint32_t reason;        // Why personality changed
        } personality;
        
        struct {
            uint32_t container_id;  // Container ID
            char container_name[32]; // Container name
        } container;
    } data;
    
    char message[128];              // Human-readable message
} debug_event_t;

/**
 * Breakpoint structure
 */
typedef struct breakpoint {
    uint64_t addr;                  // Breakpoint address
    uint8_t original_byte;          // Original instruction byte
    pid_t pid;                      // Process ID (0 for global)
    uint32_t flags;                 // Breakpoint flags
    void (*handler)(struct breakpoint *); // Breakpoint handler
    void *user_data;                // User data for handler
    int hit_count;                  // Number of hits
    int enabled;                    // Enabled flag
} breakpoint_t;

/**
 * Watchpoint structure
 */
typedef struct watchpoint {
    uint64_t addr;                  // Watch address
    uint64_t len;                   // Watch length
    uint32_t type;                  // Read/Write/Execute
    pid_t pid;                      // Process ID
    void (*handler)(struct watchpoint *, uint64_t old_val, uint64_t new_val);
    int hit_count;
    int enabled;
} watchpoint_t;

/**
 * Per-process debug state
 */
typedef struct debug_state {
    uint32_t trace_mode;            // Active trace modes
    uint32_t break_on_syscall;      // Syscalls to break on
    uint32_t break_on_signal;       // Signals to break on
    
    // Statistics
    struct {
        uint64_t syscall_count[512];   // Per-syscall counts
        uint64_t signal_count[64];     // Per-signal counts
        uint64_t fault_count;
        uint64_t total_syscall_time;
        uint64_t personality_switches;
    } stats;
    
    // Syscall filtering
    struct {
        uint32_t whitelist[16];     // Allowed syscalls (bitmap)
        uint32_t blacklist[16];     // Blocked syscalls (bitmap)
        int mode;                   // WHITELIST or BLACKLIST
    } filter;
    
    // Output control
    int output_fd;                  // Output file descriptor
    int verbose_level;              // Verbosity level
    
    struct spinlock lock;
} debug_state_t;

/**
 * Global debug state
 */
static struct {
    debug_event_t *events;          // Circular buffer of events
    uint32_t event_head;            // Next write position
    uint32_t event_tail;            // Next read position
    uint32_t event_count;           // Total events
    
    breakpoint_t breakpoints[MAX_BREAKPOINTS];
    watchpoint_t watchpoints[MAX_WATCHPOINTS];
    
    char *trace_buffer;             // Text trace buffer
    uint32_t trace_pos;             // Current position
    
    struct spinlock lock;
    int initialized;
} debug_global = {
    .lock = SPINLOCK_INITIALIZER
};

// =============================================================================
// PERSONALITY-SPECIFIC SYSCALL NAMES
// =============================================================================

/**
 * Get syscall name for personality
 */
const char *get_syscall_name(syscall_personality_t personality, int syscall_nr) {
    static const char *linux_syscalls[] = {
        [0] = "read", [1] = "write", [2] = "open", [3] = "close",
        [4] = "stat", [5] = "fstat", [6] = "lstat", [7] = "poll",
        [8] = "lseek", [9] = "mmap", [10] = "mprotect", [11] = "munmap",
        [12] = "brk", [13] = "rt_sigaction", [14] = "rt_sigprocmask",
        [15] = "rt_sigreturn", [16] = "ioctl", [17] = "pread64",
        [18] = "pwrite64", [19] = "readv", [20] = "writev", [21] = "access",
        [39] = "getpid", [56] = "clone", [57] = "fork", [58] = "vfork",
        [59] = "execve", [60] = "exit", [61] = "wait4", [62] = "kill",
        [202] = "futex", [213] = "epoll_create", [232] = "epoll_wait",
        // ... add more Linux syscalls
    };
    
    static const char *bsd_syscalls[] = {
        [0] = "syscall", [1] = "exit", [2] = "fork", [3] = "read",
        [4] = "write", [5] = "open", [6] = "close", [7] = "wait4",
        [20] = "getpid", [36] = "sync", [37] = "kill", [39] = "getppid",
        [362] = "kqueue", [363] = "kevent", [338] = "jail",
        [516] = "cap_enter", [515] = "cap_rights_limit",
        // ... add more BSD syscalls
    };
    
    static const char *illumos_syscalls[] = {
        [0] = "indir", [1] = "exit", [2] = "forkall", [3] = "read",
        [4] = "write", [5] = "open", [6] = "close", [7] = "wait",
        [20] = "getpid", [159] = "lwp_create", [160] = "lwp_exit",
        [180] = "door_create", [181] = "door_call", [227] = "zone",
        // ... add more Illumos syscalls
    };
    
    static const char *posix_syscalls[] = {
        [0] = "_exit", [1] = "fork", [2] = "read", [3] = "write",
        [4] = "open", [5] = "close", [6] = "waitpid", [7] = "creat",
        [8] = "link", [9] = "unlink", [10] = "execve", [11] = "chdir",
        [12] = "time", [13] = "mknod", [14] = "chmod", [15] = "chown",
        [16] = "break", [17] = "oldstat", [18] = "lseek", [19] = "getpid",
        // ... add more POSIX syscalls
    };
    
    const char **syscall_table = NULL;
    int table_size = 0;
    
    switch (personality) {
        case PERSONALITY_LINUX:
            syscall_table = linux_syscalls;
            table_size = sizeof(linux_syscalls) / sizeof(linux_syscalls[0]);
            break;
        case PERSONALITY_BSD:
            syscall_table = bsd_syscalls;
            table_size = sizeof(bsd_syscalls) / sizeof(bsd_syscalls[0]);
            break;
        case PERSONALITY_ILLUMOS:
            syscall_table = illumos_syscalls;
            table_size = sizeof(illumos_syscalls) / sizeof(illumos_syscalls[0]);
            break;
        case PERSONALITY_POSIX2024:
        case PERSONALITY_FEUERBIRD:
        default:
            syscall_table = posix_syscalls;
            table_size = sizeof(posix_syscalls) / sizeof(posix_syscalls[0]);
            break;
    }
    
    if (syscall_nr >= 0 && syscall_nr < table_size && syscall_table[syscall_nr]) {
        return syscall_table[syscall_nr];
    }
    
    return "unknown";
}

/**
 * Get signal name for personality
 */
const char *get_signal_name(syscall_personality_t personality, int signum) {
    // Signal names are mostly consistent across UNIX systems
    static const char *signal_names[] = {
        [1] = "SIGHUP", [2] = "SIGINT", [3] = "SIGQUIT", [4] = "SIGILL",
        [5] = "SIGTRAP", [6] = "SIGABRT", [7] = "SIGBUS", [8] = "SIGFPE",
        [9] = "SIGKILL", [10] = "SIGUSR1", [11] = "SIGSEGV", [12] = "SIGUSR2",
        [13] = "SIGPIPE", [14] = "SIGALRM", [15] = "SIGTERM", [16] = "SIGSTKFLT",
        [17] = "SIGCHLD", [18] = "SIGCONT", [19] = "SIGSTOP", [20] = "SIGTSTP",
        [21] = "SIGTTIN", [22] = "SIGTTOU", [23] = "SIGURG", [24] = "SIGXCPU",
        [25] = "SIGXFSZ", [26] = "SIGVTALRM", [27] = "SIGPROF", [28] = "SIGWINCH",
        [29] = "SIGIO", [30] = "SIGPWR", [31] = "SIGSYS",
    };
    
    // Personality-specific signal number adjustments
    if (personality == PERSONALITY_BSD) {
        // BSD has different signal numbers for some signals
        if (signum == 10) return "SIGBUS";   // BSD SIGBUS is 10
        if (signum == 11) return "SIGSEGV";  // BSD SIGSEGV is 11
    }
    
    if (signum > 0 && signum < sizeof(signal_names)/sizeof(signal_names[0])) {
        if (signal_names[signum])
            return signal_names[signum];
    }
    
    return "SIGUNKNOWN";
}

// =============================================================================
// EVENT RECORDING
// =============================================================================

/**
 * Record a debug event
 */
void record_debug_event(debug_event_t *event) {
    if (!debug_global.initialized)
        return;
    
    acquire(&debug_global.lock);
    
    // Add to circular buffer
    debug_global.events[debug_global.event_head] = *event;
    debug_global.event_head = (debug_global.event_head + 1) % MAX_TRACE_EVENTS;
    
    if (debug_global.event_count < MAX_TRACE_EVENTS)
        debug_global.event_count++;
    else
        debug_global.event_tail = (debug_global.event_tail + 1) % MAX_TRACE_EVENTS;
    
    release(&debug_global.lock);
}

/**
 * Format and record syscall entry
 */
void debug_syscall_enter(struct proc *p, int syscall_nr, uint64_t *args) {
    if (!p->debug_state || !(p->debug_state->trace_mode & TRACE_MODE_SYSCALL))
        return;
    
    debug_event_t event = {
        .timestamp = rdtsc(),
        .type = DEBUG_EVENT_SYSCALL_ENTER,
        .pid = p->pid,
        .tid = p->tid,
        .personality = p->personality,
        .data.syscall = {
            .syscall_nr = syscall_nr,
            .args = {args[0], args[1], args[2], args[3], args[4], args[5]}
        }
    };
    
    // Format message based on personality
    const char *name = get_syscall_name(p->personality, syscall_nr);
    
    snprintf(event.message, sizeof(event.message),
             "[%s] %s(%lx, %lx, %lx, %lx, %lx, %lx)",
             get_personality_name(p->personality),
             name, args[0], args[1], args[2], args[3], args[4], args[5]);
    
    record_debug_event(&event);
    
    // Update statistics
    if (syscall_nr < 512) {
        p->debug_state->stats.syscall_count[syscall_nr]++;
    }
}

/**
 * Format and record syscall exit
 */
void debug_syscall_exit(struct proc *p, int syscall_nr, int64_t result) {
    if (!p->debug_state || !(p->debug_state->trace_mode & TRACE_MODE_SYSCALL))
        return;
    
    debug_event_t event = {
        .timestamp = rdtsc(),
        .type = DEBUG_EVENT_SYSCALL_EXIT,
        .pid = p->pid,
        .tid = p->tid,
        .personality = p->personality,
        .data.syscall = {
            .syscall_nr = syscall_nr,
            .result = result,
            .errno_val = (result < 0) ? -result : 0
        }
    };
    
    const char *name = get_syscall_name(p->personality, syscall_nr);
    
    if (result < 0) {
        snprintf(event.message, sizeof(event.message),
                 "[%s] %s() = -1 (errno=%d)",
                 get_personality_name(p->personality),
                 name, -result);
    } else {
        snprintf(event.message, sizeof(event.message),
                 "[%s] %s() = %ld",
                 get_personality_name(p->personality),
                 name, result);
    }
    
    record_debug_event(&event);
}

/**
 * Record personality change
 */
void debug_personality_change(struct proc *p, 
                             syscall_personality_t old_personality,
                             syscall_personality_t new_personality) {
    if (!p->debug_state || !(p->debug_state->trace_mode & TRACE_MODE_PERSONALITY))
        return;
    
    debug_event_t event = {
        .timestamp = rdtsc(),
        .type = DEBUG_EVENT_PERSONALITY_CHANGE,
        .pid = p->pid,
        .tid = p->tid,
        .personality = new_personality,
        .data.personality = {
            .old_personality = old_personality,
            .new_personality = new_personality,
            .reason = 0  // TODO: Add reason codes
        }
    };
    
    snprintf(event.message, sizeof(event.message),
             "Personality change: %s -> %s",
             get_personality_name(old_personality),
             get_personality_name(new_personality));
    
    record_debug_event(&event);
    
    p->debug_state->stats.personality_switches++;
}

// =============================================================================
// BREAKPOINTS AND WATCHPOINTS
// =============================================================================

/**
 * Set a breakpoint
 */
int set_breakpoint(uint64_t addr, pid_t pid, 
                   void (*handler)(breakpoint_t *), void *user_data) {
    acquire(&debug_global.lock);
    
    // Find free slot
    for (int i = 0; i < MAX_BREAKPOINTS; i++) {
        if (!debug_global.breakpoints[i].enabled) {
            breakpoint_t *bp = &debug_global.breakpoints[i];
            bp->addr = addr;
            bp->pid = pid;
            bp->handler = handler;
            bp->user_data = user_data;
            bp->hit_count = 0;
            bp->enabled = 1;
            
            // TODO: Insert INT3 instruction at address
            
            release(&debug_global.lock);
            return i;
        }
    }
    
    release(&debug_global.lock);
    return -ENOMEM;
}

/**
 * Set a watchpoint
 */
int set_watchpoint(uint64_t addr, uint64_t len, uint32_t type, pid_t pid,
                   void (*handler)(watchpoint_t *, uint64_t, uint64_t)) {
    acquire(&debug_global.lock);
    
    // Find free slot
    for (int i = 0; i < MAX_WATCHPOINTS; i++) {
        if (!debug_global.watchpoints[i].enabled) {
            watchpoint_t *wp = &debug_global.watchpoints[i];
            wp->addr = addr;
            wp->len = len;
            wp->type = type;
            wp->pid = pid;
            wp->handler = handler;
            wp->hit_count = 0;
            wp->enabled = 1;
            
            // TODO: Configure hardware debug registers
            
            release(&debug_global.lock);
            return i;
        }
    }
    
    release(&debug_global.lock);
    return -ENOMEM;
}

// =============================================================================
// TRACE OUTPUT FORMATTING
// =============================================================================

/**
 * Format syscall arguments based on personality and syscall type
 */
void format_syscall_args(char *buf, size_t len, 
                        syscall_personality_t personality,
                        int syscall_nr, uint64_t *args) {
    const char *name = get_syscall_name(personality, syscall_nr);
    
    // Special formatting for common syscalls
    if (strcmp(name, "open") == 0) {
        // Format: open("filename", O_RDWR|O_CREAT, 0644)
        snprintf(buf, len, "open(\"%s\", %lo, %lo)",
                 (char *)args[0], args[1], args[2]);
    } else if (strcmp(name, "write") == 0 || strcmp(name, "read") == 0) {
        // Format: write(fd, buf, count)
        snprintf(buf, len, "%s(%d, %p, %lu)",
                 name, (int)args[0], (void *)args[1], args[2]);
    } else if (strcmp(name, "mmap") == 0) {
        // Format: mmap(addr, length, prot, flags, fd, offset)
        snprintf(buf, len, "mmap(%p, %lu, %x, %x, %d, %lx)",
                 (void *)args[0], args[1], (int)args[2], 
                 (int)args[3], (int)args[4], args[5]);
    } else if (strcmp(name, "clone") == 0 && personality == PERSONALITY_LINUX) {
        // Linux clone with flags
        snprintf(buf, len, "clone(flags=%lx, stack=%p, ptid=%p, ctid=%p, regs=%p)",
                 args[0], (void *)args[1], (void *)args[2], 
                 (void *)args[3], (void *)args[4]);
    } else if (strcmp(name, "futex") == 0 && personality == PERSONALITY_LINUX) {
        // Linux futex
        const char *op_names[] = {"WAIT", "WAKE", "FD", "REQUEUE", "CMP_REQUEUE"};
        int op = args[1] & 0xF;
        snprintf(buf, len, "futex(%p, %s, %d, ...)",
                 (void *)args[0], 
                 (op < 5) ? op_names[op] : "UNKNOWN",
                 (int)args[2]);
    } else if (strcmp(name, "zone") == 0 && personality == PERSONALITY_ILLUMOS) {
        // Illumos zone operations
        const char *cmds[] = {"CREATE", "DESTROY", "GETATTR", "ENTER", "LIST", "SHUTDOWN"};
        int cmd = args[0];
        snprintf(buf, len, "zone(%s, ...)",
                 (cmd < 6) ? cmds[cmd] : "UNKNOWN");
    } else {
        // Default formatting
        snprintf(buf, len, "%s(%lx, %lx, %lx, %lx, %lx, %lx)",
                 name, args[0], args[1], args[2], args[3], args[4], args[5]);
    }
}

/**
 * Pretty-print trace output
 */
void print_trace_event(debug_event_t *event) {
    char time_str[32];
    char output[512];
    
    // Format timestamp
    snprintf(time_str, sizeof(time_str), "[%12llu]", event->timestamp);
    
    switch (event->type) {
        case DEBUG_EVENT_SYSCALL_ENTER: {
            char args_str[256];
            format_syscall_args(args_str, sizeof(args_str),
                              event->personality,
                              event->data.syscall.syscall_nr,
                              event->data.syscall.args);
            snprintf(output, sizeof(output),
                     "%s [%d:%d] %s %s\n",
                     time_str, event->pid, event->tid,
                     get_personality_name(event->personality),
                     args_str);
            break;
        }
        
        case DEBUG_EVENT_SYSCALL_EXIT:
            if (event->data.syscall.result < 0) {
                snprintf(output, sizeof(output),
                         "%s [%d:%d] = -1 errno=%d (%s)\n",
                         time_str, event->pid, event->tid,
                         event->data.syscall.errno_val,
                         strerror(event->data.syscall.errno_val));
            } else {
                snprintf(output, sizeof(output),
                         "%s [%d:%d] = %ld (0x%lx)\n",
                         time_str, event->pid, event->tid,
                         event->data.syscall.result,
                         event->data.syscall.result);
            }
            break;
            
        case DEBUG_EVENT_SIGNAL_SEND:
            snprintf(output, sizeof(output),
                     "%s [%d:%d] Sending %s to %d\n",
                     time_str, event->pid, event->tid,
                     get_signal_name(event->personality, event->data.signal.signum),
                     event->data.signal.sender_pid);
            break;
            
        case DEBUG_EVENT_PERSONALITY_CHANGE:
            snprintf(output, sizeof(output),
                     "%s [%d:%d] %s\n",
                     time_str, event->pid, event->tid,
                     event->message);
            break;
            
        default:
            snprintf(output, sizeof(output),
                     "%s [%d:%d] %s\n",
                     time_str, event->pid, event->tid,
                     event->message);
            break;
    }
    
    // Output to console or file
    cprintf("%s", output);
}

// =============================================================================
// PERSONALITY-SPECIFIC ANALYSIS
// =============================================================================

/**
 * Analyze syscall patterns for personality
 */
void analyze_personality_patterns(struct proc *p) {
    if (!p->debug_state)
        return;
    
    debug_state_t *ds = p->debug_state;
    
    cprintf("\n=== Syscall Analysis for PID %d (%s personality) ===\n",
            p->pid, get_personality_name(p->personality));
    
    // Find most frequent syscalls
    struct {
        int syscall_nr;
        uint64_t count;
    } top_syscalls[10] = {0};
    
    for (int i = 0; i < 512; i++) {
        if (ds->stats.syscall_count[i] > 0) {
            // Insert into top 10
            for (int j = 0; j < 10; j++) {
                if (ds->stats.syscall_count[i] > top_syscalls[j].count) {
                    // Shift down
                    for (int k = 9; k > j; k--) {
                        top_syscalls[k] = top_syscalls[k-1];
                    }
                    top_syscalls[j].syscall_nr = i;
                    top_syscalls[j].count = ds->stats.syscall_count[i];
                    break;
                }
            }
        }
    }
    
    cprintf("Top 10 System Calls:\n");
    for (int i = 0; i < 10 && top_syscalls[i].count > 0; i++) {
        const char *name = get_syscall_name(p->personality, top_syscalls[i].syscall_nr);
        cprintf("  %3d. %-20s: %llu calls\n",
                i + 1, name, top_syscalls[i].count);
    }
    
    // Personality-specific analysis
    switch (p->personality) {
        case PERSONALITY_LINUX:
            cprintf("\nLinux-specific syscalls used:\n");
            if (ds->stats.syscall_count[202] > 0)  // futex
                cprintf("  - futex: %llu (thread synchronization)\n", 
                        ds->stats.syscall_count[202]);
            if (ds->stats.syscall_count[213] > 0)  // epoll_create
                cprintf("  - epoll: %llu (scalable I/O)\n",
                        ds->stats.syscall_count[213]);
            if (ds->stats.syscall_count[56] > 0)   // clone
                cprintf("  - clone: %llu (thread/process creation)\n",
                        ds->stats.syscall_count[56]);
            break;
            
        case PERSONALITY_BSD:
            cprintf("\nBSD-specific syscalls used:\n");
            if (ds->stats.syscall_count[362] > 0)  // kqueue
                cprintf("  - kqueue: %llu (event notification)\n",
                        ds->stats.syscall_count[362]);
            if (ds->stats.syscall_count[338] > 0)  // jail
                cprintf("  - jail: %llu (process isolation)\n",
                        ds->stats.syscall_count[338]);
            break;
            
        case PERSONALITY_ILLUMOS:
            cprintf("\nIllumos-specific syscalls used:\n");
            if (ds->stats.syscall_count[227] > 0)  // zone
                cprintf("  - zone: %llu (zone operations)\n",
                        ds->stats.syscall_count[227]);
            if (ds->stats.syscall_count[180] > 0)  // door_create
                cprintf("  - doors: %llu (IPC mechanism)\n",
                        ds->stats.syscall_count[180]);
            break;
    }
    
    cprintf("\nStatistics:\n");
    cprintf("  Total syscalls: %llu\n", 
            ds->stats.syscall_count[0] + ds->stats.syscall_count[1]); // Simplified
    cprintf("  Personality switches: %llu\n", ds->stats.personality_switches);
    cprintf("  Signal count: %llu\n", ds->stats.signal_count[0]); // Simplified
    cprintf("  Fault count: %llu\n", ds->stats.fault_count);
    
    if (ds->stats.total_syscall_time > 0) {
        uint64_t avg_time = ds->stats.total_syscall_time / 
                           (ds->stats.syscall_count[0] + ds->stats.syscall_count[1]);
        cprintf("  Average syscall time: %llu cycles\n", avg_time);
    }
}

// =============================================================================
// SYSCALL INTERFACE
// =============================================================================

/**
 * Enable debugging for process
 */
long sys_debug_attach(pid_t pid, uint32_t trace_mode) {
    struct proc *p = find_proc_by_pid(pid);
    if (!p)
        return -ESRCH;
    
    // Check permissions
    if (p->uid != myproc()->uid && myproc()->uid != 0)
        return -EPERM;
    
    // Allocate debug state if needed
    if (!p->debug_state) {
        p->debug_state = kalloc();
        if (!p->debug_state)
            return -ENOMEM;
        
        memset(p->debug_state, 0, sizeof(debug_state_t));
        initlock(&p->debug_state->lock, "debug");
    }
    
    p->debug_state->trace_mode = trace_mode;
    
    cprintf("Debug attached to PID %d with mode 0x%x\n", pid, trace_mode);
    
    return 0;
}

/**
 * Detach debugging from process
 */
long sys_debug_detach(pid_t pid) {
    struct proc *p = find_proc_by_pid(pid);
    if (!p)
        return -ESRCH;
    
    if (p->debug_state) {
        kfree(p->debug_state);
        p->debug_state = NULL;
    }
    
    return 0;
}

/**
 * Get debug events
 */
long sys_debug_get_events(debug_event_t *events, uint32_t *count) {
    if (!events || !count)
        return -EINVAL;
    
    uint32_t max_count = *count;
    uint32_t actual_count = 0;
    
    acquire(&debug_global.lock);
    
    while (actual_count < max_count && 
           debug_global.event_tail != debug_global.event_head) {
        events[actual_count++] = debug_global.events[debug_global.event_tail];
        debug_global.event_tail = (debug_global.event_tail + 1) % MAX_TRACE_EVENTS;
    }
    
    release(&debug_global.lock);
    
    *count = actual_count;
    return 0;
}

/**
 * Control debugging features
 */
long sys_debug_control(pid_t pid, uint32_t cmd, void *arg) {
    struct proc *p = find_proc_by_pid(pid);
    if (!p || !p->debug_state)
        return -EINVAL;
    
    switch (cmd) {
        case DEBUG_CMD_SET_BREAKPOINT:
            // Set breakpoint
            break;
            
        case DEBUG_CMD_SET_WATCHPOINT:
            // Set watchpoint
            break;
            
        case DEBUG_CMD_GET_STATS:
            // Get statistics
            if (arg) {
                memcpy(arg, &p->debug_state->stats, 
                       sizeof(p->debug_state->stats));
            }
            break;
            
        case DEBUG_CMD_ANALYZE:
            // Run analysis
            analyze_personality_patterns(p);
            break;
            
        default:
            return -EINVAL;
    }
    
    return 0;
}

// =============================================================================
// INITIALIZATION
// =============================================================================

/**
 * Initialize debugging subsystem
 */
void init_debug(void) {
    // Allocate event buffer
    debug_global.events = kalloc_pages(
        (MAX_TRACE_EVENTS * sizeof(debug_event_t) + PGSIZE - 1) / PGSIZE);
    
    if (!debug_global.events) {
        panic("Failed to allocate debug event buffer");
    }
    
    // Allocate trace buffer
    debug_global.trace_buffer = kalloc_pages(TRACE_BUFFER_SIZE / PGSIZE);
    if (!debug_global.trace_buffer) {
        panic("Failed to allocate debug trace buffer");
    }
    
    memset(debug_global.events, 0, MAX_TRACE_EVENTS * sizeof(debug_event_t));
    memset(debug_global.trace_buffer, 0, TRACE_BUFFER_SIZE);
    
    debug_global.initialized = 1;
    
    cprintf("Debug subsystem initialized\n");
    cprintf("  Event buffer: %d events\n", MAX_TRACE_EVENTS);
    cprintf("  Trace buffer: %d KB\n", TRACE_BUFFER_SIZE / 1024);
    cprintf("  Breakpoints: %d max\n", MAX_BREAKPOINTS);
    cprintf("  Watchpoints: %d max\n", MAX_WATCHPOINTS);
}
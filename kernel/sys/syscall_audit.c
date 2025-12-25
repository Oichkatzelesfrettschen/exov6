/**
 * @file syscall_audit.c
 * @brief Syscall auditing and security enforcement layer
 * 
 * Provides comprehensive syscall auditing, filtering, and security
 * policies for the multi-personality gateway.
 */

#include "syscall_gateway.h"
#include "syscall_audit.h"
#include "types.h"
#include "defs.h"
#include "param.h"
#include "proc.h"
#include "spinlock.h"
#include "fs.h"
#include "file.h"

// =============================================================================
// AUDIT CONFIGURATION
// =============================================================================

// Audit levels
#define AUDIT_NONE      0
#define AUDIT_ERRORS    1
#define AUDIT_IMPORTANT 2
#define AUDIT_VERBOSE   3
#define AUDIT_DEBUG     4

// Audit ring buffer
#define AUDIT_BUFFER_SIZE 65536
#define AUDIT_ENTRY_MAX   256

struct audit_entry {
    uint64_t timestamp;
    int pid;
    int uid;
    syscall_personality_t personality;
    int syscall_nr;
    long result;
    int error;
    char args[128];  // Serialized arguments
};

struct audit_buffer {
    struct audit_entry entries[AUDIT_BUFFER_SIZE];
    int head;
    int tail;
    struct spinlock lock;
    int dropped;  // Count of dropped entries
};

static struct audit_buffer audit_ring;
static int audit_level = AUDIT_ERRORS;
static bool audit_enabled = true;

// =============================================================================
// SECCOMP-STYLE FILTERING
// =============================================================================

// Filter actions
#define SECCOMP_RET_KILL_PROCESS   0x80000000
#define SECCOMP_RET_KILL_THREAD    0x00000000
#define SECCOMP_RET_TRAP            0x00030000
#define SECCOMP_RET_ERRNO           0x00050000
#define SECCOMP_RET_TRACE           0x7ff00000
#define SECCOMP_RET_LOG             0x7ffc0000
#define SECCOMP_RET_ALLOW           0x7fff0000

struct seccomp_filter {
    int syscall_nr;
    syscall_personality_t personality;
    uint32_t action;
    int errno_val;  // For SECCOMP_RET_ERRNO
    struct seccomp_filter *next;
};

// Per-process filter chains
struct process_filters {
    struct seccomp_filter *filters[PERSONALITY_MAX];
    int filter_count;
    uint32_t default_action;
    struct spinlock lock;
};

// Global filter policies
static struct seccomp_filter *global_filters[PERSONALITY_MAX];
static struct spinlock filter_lock;

// =============================================================================
// SYSCALL STATISTICS
// =============================================================================

struct syscall_stats_entry {
    uint64_t count;
    uint64_t total_time;
    uint64_t max_time;
    uint64_t min_time;
    uint64_t errors;
};

static struct syscall_stats_entry stats[PERSONALITY_MAX][512];  // Up to 512 syscalls per personality
static struct spinlock stats_lock;

// =============================================================================
// CAPABILITY-BASED ACCESS CONTROL
// =============================================================================

// Capability requirements per syscall
struct syscall_capability {
    int syscall_nr;
    uint64_t required_caps;
};

// Linux capabilities (simplified)
#define CAP_CHOWN           (1ULL << 0)
#define CAP_DAC_OVERRIDE    (1ULL << 1)
#define CAP_DAC_READ_SEARCH (1ULL << 2)
#define CAP_FOWNER          (1ULL << 3)
#define CAP_FSETID          (1ULL << 4)
#define CAP_KILL            (1ULL << 5)
#define CAP_SETGID          (1ULL << 6)
#define CAP_SETUID          (1ULL << 7)
#define CAP_SETPCAP         (1ULL << 8)
#define CAP_NET_BIND_SERVICE (1ULL << 10)
#define CAP_NET_ADMIN       (1ULL << 12)
#define CAP_NET_RAW         (1ULL << 13)
#define CAP_SYS_MODULE      (1ULL << 16)
#define CAP_SYS_RAWIO       (1ULL << 17)
#define CAP_SYS_CHROOT      (1ULL << 18)
#define CAP_SYS_PTRACE      (1ULL << 19)
#define CAP_SYS_ADMIN       (1ULL << 21)
#define CAP_SYS_BOOT        (1ULL << 22)
#define CAP_SYS_NICE        (1ULL << 23)
#define CAP_SYS_RESOURCE    (1ULL << 24)
#define CAP_SYS_TIME        (1ULL << 25)
#define CAP_MKNOD           (1ULL << 27)

static struct syscall_capability linux_caps[] = {
    {LINUX_SYS_chown, CAP_CHOWN},
    {LINUX_SYS_setuid, CAP_SETUID},
    {LINUX_SYS_setgid, CAP_SETGID},
    {LINUX_SYS_kill, CAP_KILL},
    {LINUX_SYS_chroot, CAP_SYS_CHROOT},
    {LINUX_SYS_mount, CAP_SYS_ADMIN},
    {LINUX_SYS_reboot, CAP_SYS_BOOT},
    {LINUX_SYS_init_module, CAP_SYS_MODULE},
    {LINUX_SYS_delete_module, CAP_SYS_MODULE},
    {LINUX_SYS_ptrace, CAP_SYS_PTRACE},
    {LINUX_SYS_mknod, CAP_MKNOD},
    {0, 0}
};

// =============================================================================
// AUDIT IMPLEMENTATION
// =============================================================================

/**
 * Initialize audit system
 */
void audit_init(void) {
    initlock(&audit_ring.lock, "audit");
    initlock(&filter_lock, "filter");
    initlock(&stats_lock, "stats");
    
    audit_ring.head = 0;
    audit_ring.tail = 0;
    audit_ring.dropped = 0;
    
    memset(stats, 0, sizeof(stats));
    
    cprintf("Syscall audit system initialized\n");
}

/**
 * Record syscall audit entry
 */
void audit_syscall(struct proc *p, int syscall_nr, long result,
                  unsigned long arg0, unsigned long arg1,
                  unsigned long arg2, unsigned long arg3,
                  unsigned long arg4, unsigned long arg5) {
    if (!audit_enabled)
        return;
    
    // Check audit level
    if (result < 0 && audit_level < AUDIT_ERRORS)
        return;
    if (result >= 0 && audit_level < AUDIT_VERBOSE)
        return;
    
    acquire(&audit_ring.lock);
    
    // Check if buffer is full
    int next = (audit_ring.head + 1) % AUDIT_BUFFER_SIZE;
    if (next == audit_ring.tail) {
        audit_ring.dropped++;
        release(&audit_ring.lock);
        return;
    }
    
    // Create audit entry
    struct audit_entry *entry = &audit_ring.entries[audit_ring.head];
    entry->timestamp = rdtsc();
    entry->pid = p->pid;
    entry->uid = p->uid;
    entry->personality = p->personality;
    entry->syscall_nr = syscall_nr;
    entry->result = result;
    entry->error = (result < 0) ? -result : 0;
    
    // Format arguments (simplified)
    snprintf(entry->args, sizeof(entry->args),
            "%lx,%lx,%lx,%lx,%lx,%lx",
            arg0, arg1, arg2, arg3, arg4, arg5);
    
    audit_ring.head = next;
    
    release(&audit_ring.lock);
    
    // Update statistics
    update_syscall_stats(p->personality, syscall_nr, result);
}

/**
 * Read audit entries
 */
int audit_read(char *buf, int size) {
    int bytes = 0;
    
    acquire(&audit_ring.lock);
    
    while (audit_ring.tail != audit_ring.head && bytes < size - 256) {
        struct audit_entry *entry = &audit_ring.entries[audit_ring.tail];
        
        int len = snprintf(buf + bytes, size - bytes,
                          "[%llu] PID:%d UID:%d PERS:%s CALL:%d RES:%ld ERR:%d ARGS:%s\n",
                          entry->timestamp,
                          entry->pid,
                          entry->uid,
                          get_personality_name(entry->personality),
                          entry->syscall_nr,
                          entry->result,
                          entry->error,
                          entry->args);
        
        if (len <= 0)
            break;
        
        bytes += len;
        audit_ring.tail = (audit_ring.tail + 1) % AUDIT_BUFFER_SIZE;
    }
    
    release(&audit_ring.lock);
    
    return bytes;
}

// =============================================================================
// SECCOMP FILTERING
// =============================================================================

/**
 * Add syscall filter
 */
int add_syscall_filter(struct proc *p, syscall_personality_t personality,
                       int syscall_nr, uint32_t action) {
    struct process_filters *pf = p->filters;
    
    if (!pf) {
        // Allocate filter structure
        pf = kalloc();
        if (!pf)
            return -ENOMEM;
        
        memset(pf, 0, sizeof(*pf));
        initlock(&pf->lock, "pfilter");
        pf->default_action = SECCOMP_RET_ALLOW;
        p->filters = pf;
    }
    
    acquire(&pf->lock);
    
    // Add filter to chain
    struct seccomp_filter *filter = kalloc();
    if (!filter) {
        release(&pf->lock);
        return -ENOMEM;
    }
    
    filter->syscall_nr = syscall_nr;
    filter->personality = personality;
    filter->action = action;
    filter->errno_val = (action & 0xFFFF0000) == SECCOMP_RET_ERRNO ? 
                       (action & 0xFFFF) : 0;
    
    filter->next = pf->filters[personality];
    pf->filters[personality] = filter;
    pf->filter_count++;
    
    release(&pf->lock);
    
    return 0;
}

/**
 * Check syscall against filters
 */
int check_syscall_filter(struct proc *p, syscall_personality_t personality,
                         int syscall_nr) {
    struct process_filters *pf = p->filters;
    
    // No filters = allow all
    if (!pf)
        return SECCOMP_RET_ALLOW;
    
    acquire(&pf->lock);
    
    // Check process-specific filters
    struct seccomp_filter *filter = pf->filters[personality];
    while (filter) {
        if (filter->syscall_nr == syscall_nr) {
            uint32_t action = filter->action;
            release(&pf->lock);
            
            // Handle filter action
            switch (action & 0xFFFF0000) {
                case SECCOMP_RET_KILL_PROCESS:
                    // Kill entire process
                    p->killed = 1;
                    return -EACCES;
                    
                case SECCOMP_RET_KILL_THREAD:
                    // Kill thread (simplified: kill process)
                    p->killed = 1;
                    return -EACCES;
                    
                case SECCOMP_RET_TRAP:
                    // Send SIGSYS
                    psignal(p, SIGSYS);
                    return -EACCES;
                    
                case SECCOMP_RET_ERRNO:
                    // Return specific errno
                    return -(action & 0xFFFF);
                    
                case SECCOMP_RET_TRACE:
                    // Notify tracer
                    if (p->tracer) {
                        notify_tracer(p, syscall_nr);
                    }
                    return SECCOMP_RET_ALLOW;
                    
                case SECCOMP_RET_LOG:
                    // Log and allow
                    audit_filtered_syscall(p, syscall_nr, "LOG");
                    return SECCOMP_RET_ALLOW;
                    
                case SECCOMP_RET_ALLOW:
                    return SECCOMP_RET_ALLOW;
            }
        }
        filter = filter->next;
    }
    
    // Check global filters
    release(&pf->lock);
    
    acquire(&filter_lock);
    filter = global_filters[personality];
    while (filter) {
        if (filter->syscall_nr == syscall_nr) {
            uint32_t action = filter->action;
            release(&filter_lock);
            return action;
        }
        filter = filter->next;
    }
    release(&filter_lock);
    
    // Default action
    return pf ? pf->default_action : SECCOMP_RET_ALLOW;
}

// =============================================================================
// CAPABILITY CHECKING
// =============================================================================

/**
 * Check if process has required capabilities
 */
int check_capabilities(struct proc *p, syscall_personality_t personality,
                      int syscall_nr) {
    uint64_t required_caps = 0;
    
    // Find required capabilities
    if (personality == PERSONALITY_LINUX) {
        for (int i = 0; linux_caps[i].syscall_nr; i++) {
            if (linux_caps[i].syscall_nr == syscall_nr) {
                required_caps = linux_caps[i].required_caps;
                break;
            }
        }
    }
    
    // No capabilities required
    if (required_caps == 0)
        return 0;
    
    // Check if process has capabilities
    if ((p->capabilities & required_caps) != required_caps) {
        audit_capability_denied(p, syscall_nr, required_caps);
        return -EPERM;
    }
    
    return 0;
}

// =============================================================================
// STATISTICS
// =============================================================================

/**
 * Update syscall statistics
 */
void update_syscall_stats(syscall_personality_t personality, int syscall_nr,
                         long result) {
    if (personality >= PERSONALITY_MAX || syscall_nr >= 512)
        return;
    
    acquire(&stats_lock);
    
    struct syscall_stats_entry *s = &stats[personality][syscall_nr];
    s->count++;
    
    if (result < 0)
        s->errors++;
    
    // Would track timing here
    
    release(&stats_lock);
}

/**
 * Get syscall statistics
 */
void get_syscall_statistics(char *buf, int size) {
    int bytes = 0;
    
    acquire(&stats_lock);
    
    for (int p = 0; p < PERSONALITY_MAX; p++) {
        bytes += snprintf(buf + bytes, size - bytes,
                         "\n=== %s Personality ===\n",
                         get_personality_name(p));
        
        for (int s = 0; s < 512; s++) {
            struct syscall_stats_entry *entry = &stats[p][s];
            if (entry->count == 0)
                continue;
            
            bytes += snprintf(buf + bytes, size - bytes,
                            "  Syscall %3d: %8llu calls, %6llu errors (%.2f%%)\n",
                            s, entry->count, entry->errors,
                            100.0 * entry->errors / entry->count);
            
            if (bytes >= size - 100)
                goto done;
        }
    }
    
done:
    release(&stats_lock);
}

// =============================================================================
// AUDIT HELPERS
// =============================================================================

/**
 * Audit filtered syscall
 */
void audit_filtered_syscall(struct proc *p, int syscall_nr, const char *action) {
    if (audit_level >= AUDIT_IMPORTANT) {
        cprintf("AUDIT: PID %d filtered syscall %d (%s)\n",
               p->pid, syscall_nr, action);
    }
}

/**
 * Audit capability denial
 */
void audit_capability_denied(struct proc *p, int syscall_nr, uint64_t caps) {
    if (audit_level >= AUDIT_ERRORS) {
        cprintf("AUDIT: PID %d denied syscall %d (missing caps: %llx)\n",
               p->pid, syscall_nr, caps);
    }
}

// =============================================================================
// SYSCALL RATE LIMITING
// =============================================================================

#define RATE_LIMIT_WINDOW 1000000000  // 1 second in nanoseconds
#define RATE_LIMIT_MAX    1000         // Max syscalls per window

struct rate_limit {
    uint64_t window_start;
    int count;
};

/**
 * Check syscall rate limit
 */
int check_rate_limit(struct proc *p) {
    uint64_t now = rdtsc();
    
    // Reset window if expired
    if (now - p->rate_limit.window_start > RATE_LIMIT_WINDOW) {
        p->rate_limit.window_start = now;
        p->rate_limit.count = 0;
    }
    
    // Check limit
    if (p->rate_limit.count >= RATE_LIMIT_MAX) {
        if (audit_level >= AUDIT_IMPORTANT) {
            cprintf("AUDIT: PID %d exceeded syscall rate limit\n", p->pid);
        }
        return -EAGAIN;
    }
    
    p->rate_limit.count++;
    return 0;
}

// =============================================================================
// SYSCALL PROXYING (FOR DEBUGGING)
// =============================================================================

/**
 * Proxy syscall to userspace handler
 */
int proxy_syscall(struct proc *p, int syscall_nr, unsigned long *args) {
    if (!p->syscall_proxy)
        return -ENOSYS;
    
    // Send syscall to userspace proxy
    struct proxy_request req = {
        .syscall_nr = syscall_nr,
        .args = {args[0], args[1], args[2], args[3], args[4], args[5]}
    };
    
    // Would implement userspace callback here
    // return call_userspace_proxy(p, &req);
    
    return -ENOSYS;
}

// =============================================================================
// POLICY CONFIGURATION
// =============================================================================

/**
 * Load security policy from configuration
 */
int load_security_policy(const char *policy_file) {
    // Would load policy from file
    // Format: personality syscall action
    // Example:
    //   linux 52 errno:13  # Deny umount with EACCES
    //   bsd 123 kill        # Kill on syscall 123
    //   * * log             # Log all syscalls
    
    return 0;
}

/**
 * Set audit level
 */
void set_audit_level(int level) {
    if (level >= AUDIT_NONE && level <= AUDIT_DEBUG) {
        audit_level = level;
        cprintf("Audit level set to %d\n", level);
    }
}

/**
 * Enable/disable auditing
 */
void set_audit_enabled(bool enabled) {
    audit_enabled = enabled;
    cprintf("Auditing %s\n", enabled ? "enabled" : "disabled");
}
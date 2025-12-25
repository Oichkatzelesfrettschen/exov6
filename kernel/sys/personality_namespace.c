/**
 * @file personality_namespace.c
 * @brief Container and namespace support for multi-personality system
 * 
 * Provides isolation between different personality processes similar to:
 * - Linux namespaces (PID, mount, network, IPC, UTS, user)
 * - Illumos zones
 * - BSD jails
 * - Plan 9 namespaces
 */

#include "types.h"
#include "defs.h"
#include "param.h"
#include "spinlock.h"
#include "proc.h"
#include "fs.h"
#include "file.h"
#include "syscall_gateway.h"

// =============================================================================
// NAMESPACE TYPES
// =============================================================================

// Namespace types (inspired by Linux)
#define NS_TYPE_PID     (1 << 0)   // Process ID namespace
#define NS_TYPE_MOUNT   (1 << 1)   // Mount namespace
#define NS_TYPE_NET     (1 << 2)   // Network namespace
#define NS_TYPE_IPC     (1 << 3)   // IPC namespace
#define NS_TYPE_UTS     (1 << 4)   // Hostname namespace
#define NS_TYPE_USER    (1 << 5)   // User namespace
#define NS_TYPE_CGROUP  (1 << 6)   // Control group namespace
#define NS_TYPE_TIME    (1 << 7)   // Time namespace (Linux 5.6+)

// Container states
typedef enum {
    CONTAINER_EMBRYO,       // Being created
    CONTAINER_RUNNING,      // Active
    CONTAINER_PAUSED,       // Suspended
    CONTAINER_STOPPED,      // Terminated
    CONTAINER_ZOMBIE        // Waiting for cleanup
} container_state_t;

// =============================================================================
// DATA STRUCTURES
// =============================================================================

/**
 * Namespace structure
 */
typedef struct namespace {
    uint32_t id;                    // Unique namespace ID
    uint32_t type;                  // NS_TYPE_* flags
    uint32_t refcount;              // Reference count
    struct spinlock lock;
    
    // Namespace-specific data
    union {
        struct {
            pid_t next_pid;         // Next PID to allocate
            pid_t max_pid;          // Maximum PID value
            struct proc *init;      // Namespace init process (PID 1)
        } pid_ns;
        
        struct {
            struct inode *root;     // Root directory for namespace
            struct mount *mounts;   // Mount list
            int mount_count;
        } mount_ns;
        
        struct {
            char hostname[64];      // Namespace hostname
            char domainname[64];    // Domain name
        } uts_ns;
        
        struct {
            uid_t uid_map[32];      // UID mappings
            gid_t gid_map[32];      // GID mappings
            int map_count;
        } user_ns;
        
        struct {
            void *shm_list;         // Shared memory segments
            void *sem_list;         // Semaphores
            void *msg_list;         // Message queues
        } ipc_ns;
        
        struct {
            int64_t time_offset;    // Time offset from host
            int64_t boot_time;      // Namespace boot time
        } time_ns;
    } data;
    
    struct namespace *parent;       // Parent namespace
    struct namespace *children;     // Child namespaces
    struct namespace *sibling;      // Sibling in parent's child list
} namespace_t;

/**
 * Container structure (collection of namespaces)
 */
typedef struct container {
    uint32_t id;                    // Unique container ID
    char name[64];                  // Container name
    container_state_t state;        // Current state
    syscall_personality_t personality; // Container personality
    
    // Resource limits (similar to cgroups)
    struct {
        uint64_t memory_limit;      // Memory limit in bytes
        uint64_t cpu_shares;        // CPU shares (weight)
        uint32_t max_processes;     // Process limit
        uint32_t max_files;         // Open file limit
        uint64_t disk_quota;        // Disk space limit
    } limits;
    
    // Resource usage
    struct {
        uint64_t memory_used;       // Current memory usage
        uint64_t cpu_time;          // Total CPU time used
        uint32_t process_count;     // Current process count
        uint32_t file_count;        // Open files
        uint64_t disk_used;         // Disk space used
    } usage;
    
    // Namespaces
    namespace_t *pid_ns;
    namespace_t *mount_ns;
    namespace_t *net_ns;
    namespace_t *ipc_ns;
    namespace_t *uts_ns;
    namespace_t *user_ns;
    namespace_t *time_ns;
    
    // Security
    uint32_t capabilities;          // Linux-style capabilities
    uint32_t seccomp_filter;       // Seccomp filter ID
    
    // Networking
    struct {
        uint32_t ip_addr;           // Container IP
        uint16_t port_range_start;  // Port range start
        uint16_t port_range_end;    // Port range end
        uint8_t mac_addr[6];        // Virtual MAC
    } network;
    
    struct spinlock lock;
    struct container *next;         // Next in global list
} container_t;

/**
 * Personality-specific container features
 */
typedef struct {
    syscall_personality_t personality;
    const char *name;
    uint32_t supported_namespaces;
    uint32_t default_capabilities;
    
    // Personality-specific handlers
    int (*create_container)(container_t *c);
    int (*destroy_container)(container_t *c);
    int (*enter_container)(container_t *c, struct proc *p);
    int (*leave_container)(container_t *c, struct proc *p);
} personality_container_ops_t;

// =============================================================================
// GLOBAL STATE
// =============================================================================

static struct {
    container_t *containers;
    namespace_t *namespaces;
    uint32_t next_container_id;
    uint32_t next_namespace_id;
    struct spinlock lock;
} container_state = {
    .next_container_id = 1,
    .next_namespace_id = 1,
    .lock = SPINLOCK_INITIALIZER
};

// =============================================================================
// NAMESPACE OPERATIONS
// =============================================================================

/**
 * Create a new namespace
 */
namespace_t *create_namespace(uint32_t type, namespace_t *parent) {
    namespace_t *ns = kalloc();
    if (!ns)
        return NULL;
    
    memset(ns, 0, sizeof(*ns));
    
    acquire(&container_state.lock);
    ns->id = container_state.next_namespace_id++;
    release(&container_state.lock);
    
    ns->type = type;
    ns->refcount = 1;
    ns->parent = parent;
    initlock(&ns->lock, "namespace");
    
    // Initialize namespace-specific data
    switch (type) {
        case NS_TYPE_PID:
            ns->data.pid_ns.next_pid = 1;
            ns->data.pid_ns.max_pid = 32768;
            break;
            
        case NS_TYPE_UTS:
            strcpy(ns->data.uts_ns.hostname, "container");
            strcpy(ns->data.uts_ns.domainname, "local");
            break;
            
        case NS_TYPE_USER:
            // Identity mapping by default
            for (int i = 0; i < 32; i++) {
                ns->data.user_ns.uid_map[i] = i;
                ns->data.user_ns.gid_map[i] = i;
            }
            ns->data.user_ns.map_count = 1;
            break;
            
        case NS_TYPE_TIME:
            ns->data.time_ns.time_offset = 0;
            ns->data.time_ns.boot_time = ticks;
            break;
    }
    
    // Link to parent
    if (parent) {
        acquire(&parent->lock);
        ns->sibling = parent->children;
        parent->children = ns;
        parent->refcount++;
        release(&parent->lock);
    }
    
    return ns;
}

/**
 * Clone a namespace
 */
namespace_t *clone_namespace(namespace_t *orig, int flags) {
    if (!orig)
        return NULL;
    
    namespace_t *ns = create_namespace(orig->type, orig->parent);
    if (!ns)
        return NULL;
    
    // Copy namespace data
    acquire(&orig->lock);
    
    switch (orig->type) {
        case NS_TYPE_PID:
            if (flags & CLONE_NEWPID) {
                // New PID namespace starts fresh
                ns->data.pid_ns.next_pid = 1;
            } else {
                // Share PID space
                ns->data.pid_ns = orig->data.pid_ns;
            }
            break;
            
        case NS_TYPE_MOUNT:
            if (flags & CLONE_NEWNS) {
                // Copy mount table
                ns->data.mount_ns = orig->data.mount_ns;
                // TODO: Deep copy mounts
            }
            break;
            
        case NS_TYPE_UTS:
            if (flags & CLONE_NEWUTS) {
                // Copy hostname/domainname
                ns->data.uts_ns = orig->data.uts_ns;
            }
            break;
            
        case NS_TYPE_USER:
            if (flags & CLONE_NEWUSER) {
                // Copy user mappings
                ns->data.user_ns = orig->data.user_ns;
            }
            break;
    }
    
    release(&orig->lock);
    
    return ns;
}

/**
 * Destroy a namespace
 */
void destroy_namespace(namespace_t *ns) {
    if (!ns)
        return;
    
    acquire(&ns->lock);
    
    if (--ns->refcount > 0) {
        release(&ns->lock);
        return;
    }
    
    // Cleanup namespace-specific resources
    switch (ns->type) {
        case NS_TYPE_MOUNT:
            // TODO: Unmount all mounts
            break;
            
        case NS_TYPE_IPC:
            // TODO: Cleanup IPC resources
            break;
    }
    
    // Unlink from parent
    if (ns->parent) {
        acquire(&ns->parent->lock);
        // TODO: Remove from parent's child list
        ns->parent->refcount--;
        release(&ns->parent->lock);
    }
    
    release(&ns->lock);
    kfree(ns);
}

// =============================================================================
// CONTAINER OPERATIONS
// =============================================================================

/**
 * Create a new container
 */
container_t *create_container(const char *name, syscall_personality_t personality) {
    container_t *c = kalloc();
    if (!c)
        return NULL;
    
    memset(c, 0, sizeof(*c));
    
    acquire(&container_state.lock);
    c->id = container_state.next_container_id++;
    c->next = container_state.containers;
    container_state.containers = c;
    release(&container_state.lock);
    
    strncpy(c->name, name, sizeof(c->name) - 1);
    c->personality = personality;
    c->state = CONTAINER_EMBRYO;
    initlock(&c->lock, "container");
    
    // Set default limits based on personality
    switch (personality) {
        case PERSONALITY_LINUX:
            c->limits.memory_limit = 512 * 1024 * 1024;  // 512MB
            c->limits.max_processes = 1024;
            c->limits.max_files = 1024;
            c->capabilities = 0xFFFFFFFF;  // All capabilities
            break;
            
        case PERSONALITY_BSD:
            c->limits.memory_limit = 256 * 1024 * 1024;  // 256MB
            c->limits.max_processes = 256;
            c->limits.max_files = 512;
            break;
            
        case PERSONALITY_ILLUMOS:
            c->limits.memory_limit = 1024 * 1024 * 1024;  // 1GB
            c->limits.max_processes = 2048;
            c->limits.max_files = 2048;
            c->limits.cpu_shares = 100;  // Fair share
            break;
            
        default:
            c->limits.memory_limit = 128 * 1024 * 1024;  // 128MB
            c->limits.max_processes = 128;
            c->limits.max_files = 256;
            break;
    }
    
    // Create namespaces
    c->pid_ns = create_namespace(NS_TYPE_PID, NULL);
    c->mount_ns = create_namespace(NS_TYPE_MOUNT, NULL);
    c->uts_ns = create_namespace(NS_TYPE_UTS, NULL);
    c->user_ns = create_namespace(NS_TYPE_USER, NULL);
    c->ipc_ns = create_namespace(NS_TYPE_IPC, NULL);
    c->time_ns = create_namespace(NS_TYPE_TIME, NULL);
    
    // Set container-specific UTS
    if (c->uts_ns) {
        snprintf(c->uts_ns->data.uts_ns.hostname, 64, "%s-%d", name, c->id);
    }
    
    c->state = CONTAINER_RUNNING;
    
    cprintf("Container %d (%s) created with %s personality\n",
            c->id, c->name, get_personality_name(personality));
    
    return c;
}

/**
 * Destroy a container
 */
int destroy_container(container_t *c) {
    if (!c)
        return -EINVAL;
    
    acquire(&c->lock);
    
    if (c->state == CONTAINER_RUNNING) {
        // Stop all processes in container
        // TODO: Iterate through processes and terminate
        c->state = CONTAINER_STOPPED;
    }
    
    // Destroy namespaces
    destroy_namespace(c->pid_ns);
    destroy_namespace(c->mount_ns);
    destroy_namespace(c->uts_ns);
    destroy_namespace(c->user_ns);
    destroy_namespace(c->ipc_ns);
    destroy_namespace(c->time_ns);
    
    // Remove from global list
    acquire(&container_state.lock);
    container_t **pp = &container_state.containers;
    while (*pp) {
        if (*pp == c) {
            *pp = c->next;
            break;
        }
        pp = &(*pp)->next;
    }
    release(&container_state.lock);
    
    release(&c->lock);
    
    cprintf("Container %d (%s) destroyed\n", c->id, c->name);
    
    kfree(c);
    return 0;
}

/**
 * Enter a container (process joins container)
 */
int enter_container(container_t *c, struct proc *p) {
    if (!c || !p)
        return -EINVAL;
    
    acquire(&c->lock);
    
    if (c->state != CONTAINER_RUNNING) {
        release(&c->lock);
        return -EINVAL;
    }
    
    // Check resource limits
    if (c->usage.process_count >= c->limits.max_processes) {
        release(&c->lock);
        return -ENOSPC;
    }
    
    // Set process namespaces
    p->container = c;
    p->pid_ns = c->pid_ns;
    p->mount_ns = c->mount_ns;
    p->uts_ns = c->uts_ns;
    p->user_ns = c->user_ns;
    p->ipc_ns = c->ipc_ns;
    
    // Update usage
    c->usage.process_count++;
    
    // Set personality if not already set
    if (p->personality == PERSONALITY_FEUERBIRD) {
        p->personality = c->personality;
    }
    
    // Apply capability restrictions
    p->capabilities &= c->capabilities;
    
    release(&c->lock);
    
    cprintf("Process %d entered container %d (%s)\n", p->pid, c->id, c->name);
    
    return 0;
}

/**
 * Leave a container
 */
int leave_container(container_t *c, struct proc *p) {
    if (!c || !p)
        return -EINVAL;
    
    acquire(&c->lock);
    
    // Clear process namespaces
    p->container = NULL;
    p->pid_ns = NULL;
    p->mount_ns = NULL;
    p->uts_ns = NULL;
    p->user_ns = NULL;
    p->ipc_ns = NULL;
    
    // Update usage
    c->usage.process_count--;
    
    release(&c->lock);
    
    return 0;
}

// =============================================================================
// PERSONALITY-SPECIFIC CONTAINER FEATURES
// =============================================================================

/**
 * Linux container support (Docker/LXC style)
 */
int linux_container_create(container_t *c) {
    // Set up cgroup-like resource control
    c->capabilities = CAP_ALL;  // Start with all capabilities
    
    // Remove dangerous capabilities
    c->capabilities &= ~CAP_SYS_MODULE;   // No kernel modules
    c->capabilities &= ~CAP_SYS_BOOT;     // No reboot
    c->capabilities &= ~CAP_SYS_TIME;     // No time changes
    
    // Set up network namespace with veth pair
    // TODO: Create virtual ethernet interface
    
    return 0;
}

/**
 * BSD jail support
 */
int bsd_jail_create(container_t *c) {
    // BSD jails are more restrictive
    c->capabilities = 0;  // No capabilities by default
    
    // Jails can only see their own processes
    c->pid_ns->data.pid_ns.max_pid = 1000;
    
    // Set jail-specific restrictions
    // TODO: Implement jail restrictions
    
    return 0;
}

/**
 * Illumos zone support
 */
int illumos_zone_create(container_t *c) {
    // Zones have resource pools
    c->limits.cpu_shares = 100;  // Fair share scheduling
    
    // Zones can have dedicated datasets
    // TODO: Set up ZFS dataset for zone
    
    // Set zone brand based on personality
    // TODO: Implement zone branding
    
    return 0;
}

// Personality-specific operations
static personality_container_ops_t personality_ops[] = {
    {
        .personality = PERSONALITY_LINUX,
        .name = "Linux Container",
        .supported_namespaces = NS_TYPE_PID | NS_TYPE_MOUNT | NS_TYPE_NET | 
                               NS_TYPE_IPC | NS_TYPE_UTS | NS_TYPE_USER,
        .default_capabilities = 0xFFFFFFFF,
        .create_container = linux_container_create,
    },
    {
        .personality = PERSONALITY_BSD,
        .name = "BSD Jail",
        .supported_namespaces = NS_TYPE_PID | NS_TYPE_MOUNT,
        .default_capabilities = 0,
        .create_container = bsd_jail_create,
    },
    {
        .personality = PERSONALITY_ILLUMOS,
        .name = "Illumos Zone",
        .supported_namespaces = NS_TYPE_PID | NS_TYPE_MOUNT | NS_TYPE_NET,
        .default_capabilities = 0xFFFFFFFF,
        .create_container = illumos_zone_create,
    },
};

// =============================================================================
// SYSCALL INTERFACE
// =============================================================================

/**
 * Create container syscall
 */
long sys_container_create(const char *name, syscall_personality_t personality,
                         uint32_t flags) {
    if (!name)
        return -EINVAL;
    
    if (personality >= PERSONALITY_MAX)
        return -EINVAL;
    
    container_t *c = create_container(name, personality);
    if (!c)
        return -ENOMEM;
    
    // Call personality-specific setup
    for (int i = 0; i < sizeof(personality_ops)/sizeof(personality_ops[0]); i++) {
        if (personality_ops[i].personality == personality) {
            if (personality_ops[i].create_container) {
                personality_ops[i].create_container(c);
            }
            break;
        }
    }
    
    return c->id;
}

/**
 * Enter container syscall
 */
long sys_container_enter(uint32_t container_id) {
    container_t *c = NULL;
    
    // Find container
    acquire(&container_state.lock);
    for (c = container_state.containers; c; c = c->next) {
        if (c->id == container_id)
            break;
    }
    release(&container_state.lock);
    
    if (!c)
        return -ENOENT;
    
    return enter_container(c, myproc());
}

/**
 * Container control syscall (similar to ioctl)
 */
long sys_container_ctl(uint32_t container_id, uint32_t cmd, void *arg) {
    container_t *c = NULL;
    
    // Find container
    acquire(&container_state.lock);
    for (c = container_state.containers; c; c = c->next) {
        if (c->id == container_id)
            break;
    }
    release(&container_state.lock);
    
    if (!c)
        return -ENOENT;
    
    switch (cmd) {
        case CONTAINER_CTL_PAUSE:
            c->state = CONTAINER_PAUSED;
            return 0;
            
        case CONTAINER_CTL_RESUME:
            c->state = CONTAINER_RUNNING;
            return 0;
            
        case CONTAINER_CTL_GET_STATS:
            if (arg) {
                struct container_stats *stats = arg;
                stats->memory_used = c->usage.memory_used;
                stats->process_count = c->usage.process_count;
                stats->cpu_time = c->usage.cpu_time;
            }
            return 0;
            
        case CONTAINER_CTL_SET_LIMIT:
            // TODO: Implement resource limit changes
            return 0;
            
        default:
            return -EINVAL;
    }
}

/**
 * List containers syscall
 */
long sys_container_list(uint32_t *ids, uint32_t *count) {
    if (!ids || !count)
        return -EINVAL;
    
    uint32_t max_count = *count;
    uint32_t actual_count = 0;
    
    acquire(&container_state.lock);
    
    container_t *c;
    for (c = container_state.containers; c && actual_count < max_count; c = c->next) {
        ids[actual_count++] = c->id;
    }
    
    *count = actual_count;
    
    release(&container_state.lock);
    
    return 0;
}

// =============================================================================
// INITIALIZATION
// =============================================================================

/**
 * Initialize container subsystem
 */
void init_containers(void) {
    initlock(&container_state.lock, "containers");
    
    // Create default container for init process
    container_t *root = create_container("root", PERSONALITY_FEUERBIRD);
    if (root) {
        root->limits.memory_limit = 0;  // Unlimited
        root->limits.max_processes = 0;  // Unlimited
        root->limits.max_files = 0;      // Unlimited
    }
    
    cprintf("Container subsystem initialized\n");
    cprintf("  Supported personalities:\n");
    cprintf("    - Linux containers (Docker/LXC style)\n");
    cprintf("    - BSD jails\n");
    cprintf("    - Illumos zones\n");
    cprintf("    - POSIX containers\n");
    cprintf("    - Native FeuerBird containers\n");
}
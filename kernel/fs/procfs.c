/**
 * @file procfs.c
 * @brief /proc and /sys filesystem emulation for personality compatibility
 * 
 * Provides Linux-style /proc and /sys filesystems with personality-aware
 * content generation. Different personalities see different views.
 */

#include "types.h"
#include "defs.h"
#include "param.h"
#include "stat.h"
#include "mmu.h"
#include "proc.h"
#include "spinlock.h"
#include "sleeplock.h"
#include "fs.h"
#include "file.h"
#include "syscall_gateway.h"
#include "personality_namespace.h"

// =============================================================================
// PROCFS TYPES
// =============================================================================

#define PROCFS_MAGIC    0x9fa0  // proc filesystem magic
#define SYSFS_MAGIC     0x62656572  // sysfs magic

// Procfs entry types
typedef enum {
    PROCFS_DIR,         // Directory
    PROCFS_FILE,        // Regular file
    PROCFS_LINK,        // Symbolic link
    PROCFS_PID_DIR,     // Process directory (/proc/[pid])
    PROCFS_TASK_DIR,    // Task directory (/proc/[pid]/task/[tid])
    PROCFS_NET_DIR,     // Network directory (/proc/net)
    PROCFS_SYS_DIR,     // System directory (/proc/sys)
} procfs_type_t;

// Procfs entry flags
#define PROCFS_STATIC   (1 << 0)   // Static entry (not process-specific)
#define PROCFS_DYNAMIC  (1 << 1)   // Dynamic content
#define PROCFS_WORLD_READABLE (1 << 2)  // World readable
#define PROCFS_OWNER_ONLY    (1 << 3)   // Owner access only
#define PROCFS_ROOT_ONLY     (1 << 4)   // Root access only

// =============================================================================
// DATA STRUCTURES
// =============================================================================

/**
 * Procfs directory entry
 */
typedef struct procfs_entry {
    char name[32];                  // Entry name
    procfs_type_t type;             // Entry type
    uint32_t flags;                 // Entry flags
    mode_t mode;                    // File mode
    uid_t uid;                      // Owner UID
    gid_t gid;                      // Owner GID
    
    // Content generation function
    int (*read_proc)(struct proc *p, char *buf, int size, off_t offset);
    int (*write_proc)(struct proc *p, const char *buf, int size, off_t offset);
    
    // For directories
    struct procfs_entry *children;  // Child entries
    struct procfs_entry *sibling;   // Next sibling
    struct procfs_entry *parent;    // Parent directory
    
    // For dynamic entries
    void *private_data;             // Private data
    int ref_count;                  // Reference count
} procfs_entry_t;

/**
 * Procfs superblock
 */
typedef struct procfs_sb {
    uint32_t magic;                 // Filesystem magic
    procfs_entry_t *root;           // Root directory
    struct spinlock lock;           // Filesystem lock
    int mounted;                    // Mount status
    syscall_personality_t personality; // Personality view
} procfs_sb_t;

// Global procfs instances (one per personality)
static procfs_sb_t procfs_instances[PERSONALITY_MAX];
static procfs_sb_t sysfs_instances[PERSONALITY_MAX];

// =============================================================================
// CONTENT GENERATORS FOR /proc FILES
// =============================================================================

/**
 * Generate /proc/version content
 */
static int proc_version_read(struct proc *p, char *buf, int size, off_t offset) {
    const char *version;
    
    // Different version strings per personality
    switch (p->personality) {
        case PERSONALITY_LINUX:
            version = "Linux version 6.0.0-feuerbird (gcc version 12.0.0) #1 SMP PREEMPT\n";
            break;
        case PERSONALITY_BSD:
            version = "FreeBSD 14.0-RELEASE-feuerbird #0: Thu Jan 1 00:00:00 UTC 2024\n";
            break;
        case PERSONALITY_ILLUMOS:
            version = "SunOS 5.11 illumos-feuerbird January 2024\n";
            break;
        default:
            version = "FeuerBird exokernel 1.0.0 (POSIX.1-2024 compliant)\n";
            break;
    }
    
    int len = strlen(version);
    if (offset >= len)
        return 0;
    
    int n = min(size, len - offset);
    memmove(buf, version + offset, n);
    return n;
}

/**
 * Generate /proc/cpuinfo content
 */
static int proc_cpuinfo_read(struct proc *p, char *buf, int size, off_t offset) {
    char cpuinfo[1024];
    int len = 0;
    
    // Get CPU information
    int ncpu = ncpu;  // Number of CPUs
    
    if (p->personality == PERSONALITY_LINUX) {
        // Linux-style cpuinfo
        for (int i = 0; i < ncpu; i++) {
            len += snprintf(cpuinfo + len, sizeof(cpuinfo) - len,
                "processor\t: %d\n"
                "vendor_id\t: GenuineIntel\n"
                "cpu family\t: 6\n"
                "model\t\t: 158\n"
                "model name\t: Intel(R) Core(TM) i7-9750H CPU @ 2.60GHz\n"
                "stepping\t: 10\n"
                "cpu MHz\t\t: 2600.000\n"
                "cache size\t: 12288 KB\n"
                "physical id\t: 0\n"
                "siblings\t: %d\n"
                "core id\t\t: %d\n"
                "cpu cores\t: %d\n"
                "flags\t\t: fpu vme de pse tsc msr pae mce cx8 apic\n"
                "\n", i, ncpu, i, ncpu);
        }
    } else if (p->personality == PERSONALITY_BSD) {
        // BSD-style cpuinfo
        len = snprintf(cpuinfo, sizeof(cpuinfo),
            "hw.model: Intel(R) Core(TM) i7-9750H CPU @ 2.60GHz\n"
            "hw.ncpu: %d\n"
            "hw.byteorder: 1234\n"
            "hw.pagesize: 4096\n"
            "hw.machine: amd64\n",
            ncpu);
    } else if (p->personality == PERSONALITY_ILLUMOS) {
        // Illumos-style cpuinfo
        len = snprintf(cpuinfo, sizeof(cpuinfo),
            "cpu_info:0:cpu_info0:brand      Intel(R) Core(TM) i7-9750H CPU @ 2.60GHz\n"
            "cpu_info:0:cpu_info0:family     6\n"
            "cpu_info:0:cpu_info0:model      158\n"
            "cpu_info:0:cpu_info0:stepping   10\n"
            "cpu_info:0:cpu_info0:clock_MHz  2600\n"
            "cpu_info:0:cpu_info0:ncore_per_chip %d\n",
            ncpu);
    } else {
        // Generic POSIX
        len = snprintf(cpuinfo, sizeof(cpuinfo),
            "Number of processors: %d\n"
            "Processor type: x86_64\n",
            ncpu);
    }
    
    if (offset >= len)
        return 0;
    
    int n = min(size, len - offset);
    memmove(buf, cpuinfo + offset, n);
    return n;
}

/**
 * Generate /proc/meminfo content
 */
static int proc_meminfo_read(struct proc *p, char *buf, int size, off_t offset) {
    char meminfo[512];
    int len;
    
    // Get memory statistics
    uint64_t total = PHYSTOP;  // Total physical memory
    uint64_t free = get_free_pages() * PGSIZE;
    uint64_t used = total - free;
    uint64_t buffers = 0;  // TODO: Get buffer cache size
    uint64_t cached = 0;   // TODO: Get page cache size
    
    if (p->personality == PERSONALITY_LINUX) {
        // Linux-style meminfo (in KB)
        len = snprintf(meminfo, sizeof(meminfo),
            "MemTotal:       %8llu kB\n"
            "MemFree:        %8llu kB\n"
            "MemAvailable:   %8llu kB\n"
            "Buffers:        %8llu kB\n"
            "Cached:         %8llu kB\n"
            "SwapCached:            0 kB\n"
            "Active:         %8llu kB\n"
            "Inactive:       %8llu kB\n"
            "SwapTotal:             0 kB\n"
            "SwapFree:              0 kB\n"
            "Dirty:                 0 kB\n"
            "Writeback:             0 kB\n"
            "Mapped:         %8llu kB\n"
            "Shmem:                 0 kB\n"
            "Slab:           %8llu kB\n",
            total / 1024, free / 1024, free / 1024,
            buffers / 1024, cached / 1024,
            used / 1024, 0ULL,
            used / 1024,
            cached / 1024);
    } else if (p->personality == PERSONALITY_BSD) {
        // BSD-style meminfo
        len = snprintf(meminfo, sizeof(meminfo),
            "hw.physmem: %llu\n"
            "hw.usermem: %llu\n"
            "hw.realmem: %llu\n"
            "vm.stats.vm.v_free_count: %llu\n"
            "vm.stats.vm.v_cache_count: %llu\n",
            total, used, total,
            free / PGSIZE, cached / PGSIZE);
    } else {
        // Generic
        len = snprintf(meminfo, sizeof(meminfo),
            "Total memory: %llu bytes\n"
            "Free memory: %llu bytes\n"
            "Used memory: %llu bytes\n",
            total, free, used);
    }
    
    if (offset >= len)
        return 0;
    
    int n = min(size, len - offset);
    memmove(buf, meminfo + offset, n);
    return n;
}

/**
 * Generate /proc/[pid]/status content
 */
static int proc_pid_status_read(struct proc *p, char *buf, int size, off_t offset) {
    char status[1024];
    int len;
    
    // Get process information
    struct proc *target = p;  // TODO: Get target process from inode
    
    if (p->personality == PERSONALITY_LINUX) {
        // Linux-style status
        len = snprintf(status, sizeof(status),
            "Name:\t%s\n"
            "Umask:\t0022\n"
            "State:\t%c (%s)\n"
            "Tgid:\t%d\n"
            "Ngid:\t0\n"
            "Pid:\t%d\n"
            "PPid:\t%d\n"
            "TracerPid:\t0\n"
            "Uid:\t%d\t%d\t%d\t%d\n"
            "Gid:\t%d\t%d\t%d\t%d\n"
            "FDSize:\t64\n"
            "Groups:\t\n"
            "VmPeak:\t%8lu kB\n"
            "VmSize:\t%8lu kB\n"
            "VmRSS:\t%8lu kB\n"
            "Threads:\t1\n"
            "SigPnd:\t%016llx\n"
            "SigBlk:\t%016llx\n"
            "Personality:\t%08x\n",
            target->name,
            target->state == RUNNING ? 'R' :
            target->state == SLEEPING ? 'S' :
            target->state == ZOMBIE ? 'Z' : 'D',
            target->state == RUNNING ? "running" :
            target->state == SLEEPING ? "sleeping" :
            target->state == ZOMBIE ? "zombie" : "disk sleep",
            target->pid, target->pid,
            target->parent ? target->parent->pid : 0,
            target->uid, target->uid, target->uid, target->uid,
            target->gid, target->gid, target->gid, target->gid,
            target->sz / 1024,
            target->sz / 1024,
            target->sz / 1024,
            target->pending_signals,
            target->signal_mask,
            target->personality);
    } else if (p->personality == PERSONALITY_BSD) {
        // BSD-style status
        len = snprintf(status, sizeof(status),
            "pid: %d\n"
            "ppid: %d\n"
            "pgrp: %d\n"
            "sid: %d\n"
            "tsid: %d\n"
            "uid: %d\n"
            "gid: %d\n"
            "svuid: %d\n"
            "svgid: %d\n"
            "comm: %s\n"
            "state: %s\n",
            target->pid,
            target->parent ? target->parent->pid : 0,
            target->pid,  // TODO: Process group
            target->pid,  // TODO: Session ID
            0,  // TODO: Terminal session
            target->uid, target->gid,
            target->uid, target->gid,
            target->name,
            target->state == RUNNING ? "run" :
            target->state == SLEEPING ? "sleep" :
            target->state == ZOMBIE ? "zomb" : "stop");
    } else {
        // Generic
        len = snprintf(status, sizeof(status),
            "PID: %d\n"
            "Name: %s\n"
            "State: %d\n"
            "Parent: %d\n"
            "UID: %d\n"
            "GID: %d\n",
            target->pid, target->name, target->state,
            target->parent ? target->parent->pid : 0,
            target->uid, target->gid);
    }
    
    if (offset >= len)
        return 0;
    
    int n = min(size, len - offset);
    memmove(buf, status + offset, n);
    return n;
}

/**
 * Generate /proc/[pid]/maps content (memory mappings)
 */
static int proc_pid_maps_read(struct proc *p, char *buf, int size, off_t offset) {
    char maps[2048];
    int len = 0;
    
    struct proc *target = p;  // TODO: Get target process
    
    // Generate memory map
    // TODO: Walk page table and generate actual mappings
    
    if (p->personality == PERSONALITY_LINUX) {
        // Linux-style maps
        len += snprintf(maps + len, sizeof(maps) - len,
            "00400000-00401000 r-xp 00000000 08:01 123456 %s\n"
            "00600000-00601000 r--p 00000000 08:01 123456 %s\n"
            "00601000-00602000 rw-p 00001000 08:01 123456 %s\n",
            target->name, target->name, target->name);
        
        // Stack
        len += snprintf(maps + len, sizeof(maps) - len,
            "7ffffffde000-7ffffffff000 rw-p 00000000 00:00 0 [stack]\n");
        
        // Heap
        if (target->sz > 0) {
            len += snprintf(maps + len, sizeof(maps) - len,
                "00602000-%08lx rw-p 00000000 00:00 0 [heap]\n",
                0x00602000 + target->sz);
        }
    } else if (p->personality == PERSONALITY_BSD) {
        // BSD-style maps (procstat -v format)
        len += snprintf(maps + len, sizeof(maps) - len,
            "  PID              START                END PRT  RES PRES REF SHD FLAG TP PATH\n"
            "%5d 0x400000         0x401000         r-x    1    1   1   0 CN-- vn %s\n"
            "%5d 0x7ffffffde000   0x7ffffffff000   rw-   32   32   1   0 ---- df \n",
            target->pid, target->name,
            target->pid);
    } else {
        // Generic format
        len += snprintf(maps + len, sizeof(maps) - len,
            "Text:  0x00400000-0x00401000\n"
            "Data:  0x00600000-0x00602000\n"
            "Heap:  0x00602000-0x%08lx\n"
            "Stack: 0x7ffffffde000-0x7ffffffff000\n",
            0x00602000 + target->sz);
    }
    
    if (offset >= len)
        return 0;
    
    int n = min(size, len - offset);
    memmove(buf, maps + offset, n);
    return n;
}

/**
 * Generate /proc/[pid]/cmdline content
 */
static int proc_pid_cmdline_read(struct proc *p, char *buf, int size, off_t offset) {
    struct proc *target = p;  // TODO: Get target process
    
    // Copy command line arguments
    // TODO: Get actual command line from process
    char cmdline[128];
    int len = snprintf(cmdline, sizeof(cmdline), "%s", target->name);
    
    // Replace spaces with nulls for Linux compatibility
    if (p->personality == PERSONALITY_LINUX) {
        for (int i = 0; i < len; i++) {
            if (cmdline[i] == ' ')
                cmdline[i] = '\0';
        }
    }
    
    if (offset >= len)
        return 0;
    
    int n = min(size, len - offset);
    memmove(buf, cmdline + offset, n);
    return n;
}

// =============================================================================
// CONTENT GENERATORS FOR /sys FILES
// =============================================================================

/**
 * Generate /sys/kernel/hostname content
 */
static int sys_hostname_read(struct proc *p, char *buf, int size, off_t offset) {
    char hostname[64];
    
    // Get hostname based on container/personality
    if (p->container && p->container->uts_ns) {
        strncpy(hostname, p->container->uts_ns->data.uts_ns.hostname, sizeof(hostname));
    } else {
        strncpy(hostname, "feuerbird", sizeof(hostname));
    }
    
    int len = strlen(hostname);
    if (p->personality == PERSONALITY_LINUX)
        hostname[len++] = '\n';  // Linux adds newline
    
    if (offset >= len)
        return 0;
    
    int n = min(size, len - offset);
    memmove(buf, hostname + offset, n);
    return n;
}

/**
 * Write to /sys/kernel/hostname
 */
static int sys_hostname_write(struct proc *p, const char *buf, int size, off_t offset) {
    if (p->uid != 0)
        return -EPERM;  // Only root can change hostname
    
    if (offset != 0)
        return -EINVAL;
    
    char hostname[64];
    int len = min(size, sizeof(hostname) - 1);
    memmove(hostname, buf, len);
    hostname[len] = '\0';
    
    // Remove trailing newline if present
    if (len > 0 && hostname[len - 1] == '\n')
        hostname[len - 1] = '\0';
    
    // Update hostname in namespace
    if (p->container && p->container->uts_ns) {
        strncpy(p->container->uts_ns->data.uts_ns.hostname, hostname, 64);
    }
    
    return len;
}

// =============================================================================
// PROCFS OPERATIONS
// =============================================================================

/**
 * Create a procfs entry
 */
static procfs_entry_t *create_procfs_entry(const char *name, procfs_type_t type,
                                          mode_t mode, procfs_entry_t *parent) {
    procfs_entry_t *entry = kalloc();
    if (!entry)
        return NULL;
    
    memset(entry, 0, sizeof(*entry));
    strncpy(entry->name, name, sizeof(entry->name) - 1);
    entry->type = type;
    entry->mode = mode;
    entry->parent = parent;
    entry->ref_count = 1;
    
    // Add to parent's children
    if (parent) {
        entry->sibling = parent->children;
        parent->children = entry;
    }
    
    return entry;
}

/**
 * Initialize /proc filesystem for personality
 */
static void init_procfs_personality(syscall_personality_t personality) {
    procfs_sb_t *sb = &procfs_instances[personality];
    
    sb->magic = PROCFS_MAGIC;
    sb->personality = personality;
    initlock(&sb->lock, "procfs");
    
    // Create root directory
    sb->root = create_procfs_entry("", PROCFS_DIR, 0555, NULL);
    sb->root->flags = PROCFS_STATIC | PROCFS_WORLD_READABLE;
    
    // Create common /proc entries
    procfs_entry_t *entry;
    
    // /proc/version
    entry = create_procfs_entry("version", PROCFS_FILE, 0444, sb->root);
    entry->read_proc = proc_version_read;
    entry->flags = PROCFS_STATIC | PROCFS_WORLD_READABLE;
    
    // /proc/cpuinfo
    entry = create_procfs_entry("cpuinfo", PROCFS_FILE, 0444, sb->root);
    entry->read_proc = proc_cpuinfo_read;
    entry->flags = PROCFS_STATIC | PROCFS_WORLD_READABLE;
    
    // /proc/meminfo
    entry = create_procfs_entry("meminfo", PROCFS_FILE, 0444, sb->root);
    entry->read_proc = proc_meminfo_read;
    entry->flags = PROCFS_STATIC | PROCFS_WORLD_READABLE;
    
    // /proc/uptime
    entry = create_procfs_entry("uptime", PROCFS_FILE, 0444, sb->root);
    entry->flags = PROCFS_STATIC | PROCFS_WORLD_READABLE;
    
    // /proc/loadavg
    entry = create_procfs_entry("loadavg", PROCFS_FILE, 0444, sb->root);
    entry->flags = PROCFS_STATIC | PROCFS_WORLD_READABLE;
    
    // Personality-specific entries
    if (personality == PERSONALITY_LINUX) {
        // Linux-specific /proc entries
        
        // /proc/sys directory
        procfs_entry_t *sys = create_procfs_entry("sys", PROCFS_SYS_DIR, 0555, sb->root);
        sys->flags = PROCFS_STATIC | PROCFS_WORLD_READABLE;
        
        // /proc/sys/kernel
        procfs_entry_t *kernel = create_procfs_entry("kernel", PROCFS_DIR, 0555, sys);
        kernel->flags = PROCFS_STATIC | PROCFS_WORLD_READABLE;
        
        // /proc/net directory
        procfs_entry_t *net = create_procfs_entry("net", PROCFS_NET_DIR, 0555, sb->root);
        net->flags = PROCFS_STATIC | PROCFS_WORLD_READABLE;
        
        // /proc/self symlink
        entry = create_procfs_entry("self", PROCFS_LINK, 0777, sb->root);
        entry->flags = PROCFS_DYNAMIC;
        
    } else if (personality == PERSONALITY_BSD) {
        // BSD-specific /proc entries
        
        // /proc/curproc symlink (BSD equivalent of /proc/self)
        entry = create_procfs_entry("curproc", PROCFS_LINK, 0777, sb->root);
        entry->flags = PROCFS_DYNAMIC;
        
    } else if (personality == PERSONALITY_ILLUMOS) {
        // Illumos-specific /proc entries
        
        // /proc/sysconfig
        entry = create_procfs_entry("sysconfig", PROCFS_FILE, 0444, sb->root);
        entry->flags = PROCFS_STATIC | PROCFS_WORLD_READABLE;
    }
    
    sb->mounted = 1;
}

/**
 * Initialize /sys filesystem for personality
 */
static void init_sysfs_personality(syscall_personality_t personality) {
    procfs_sb_t *sb = &sysfs_instances[personality];
    
    sb->magic = SYSFS_MAGIC;
    sb->personality = personality;
    initlock(&sb->lock, "sysfs");
    
    // Create root directory
    sb->root = create_procfs_entry("", PROCFS_DIR, 0555, NULL);
    sb->root->flags = PROCFS_STATIC | PROCFS_WORLD_READABLE;
    
    // Create /sys hierarchy (Linux-style)
    if (personality == PERSONALITY_LINUX) {
        // /sys/kernel
        procfs_entry_t *kernel = create_procfs_entry("kernel", PROCFS_DIR, 0555, sb->root);
        kernel->flags = PROCFS_STATIC | PROCFS_WORLD_READABLE;
        
        // /sys/kernel/hostname
        procfs_entry_t *hostname = create_procfs_entry("hostname", PROCFS_FILE, 0644, kernel);
        hostname->read_proc = sys_hostname_read;
        hostname->write_proc = sys_hostname_write;
        hostname->flags = PROCFS_DYNAMIC;
        
        // /sys/devices
        procfs_entry_t *devices = create_procfs_entry("devices", PROCFS_DIR, 0555, sb->root);
        devices->flags = PROCFS_STATIC | PROCFS_WORLD_READABLE;
        
        // /sys/class
        procfs_entry_t *class = create_procfs_entry("class", PROCFS_DIR, 0555, sb->root);
        class->flags = PROCFS_STATIC | PROCFS_WORLD_READABLE;
        
        // /sys/block
        procfs_entry_t *block = create_procfs_entry("block", PROCFS_DIR, 0555, sb->root);
        block->flags = PROCFS_STATIC | PROCFS_WORLD_READABLE;
        
        // /sys/fs
        procfs_entry_t *fs = create_procfs_entry("fs", PROCFS_DIR, 0555, sb->root);
        fs->flags = PROCFS_STATIC | PROCFS_WORLD_READABLE;
    }
    
    sb->mounted = 1;
}

/**
 * Create per-process entries in /proc
 */
static procfs_entry_t *create_pid_entries(struct proc *p, procfs_entry_t *root) {
    char name[16];
    snprintf(name, sizeof(name), "%d", p->pid);
    
    // Create /proc/[pid] directory
    procfs_entry_t *pid_dir = create_procfs_entry(name, PROCFS_PID_DIR, 0555, root);
    pid_dir->flags = PROCFS_DYNAMIC;
    pid_dir->uid = p->uid;
    pid_dir->gid = p->gid;
    pid_dir->private_data = p;
    
    // Create process-specific files
    procfs_entry_t *entry;
    
    // /proc/[pid]/status
    entry = create_procfs_entry("status", PROCFS_FILE, 0444, pid_dir);
    entry->read_proc = proc_pid_status_read;
    entry->flags = PROCFS_DYNAMIC;
    
    // /proc/[pid]/cmdline
    entry = create_procfs_entry("cmdline", PROCFS_FILE, 0444, pid_dir);
    entry->read_proc = proc_pid_cmdline_read;
    entry->flags = PROCFS_DYNAMIC;
    
    // /proc/[pid]/maps
    entry = create_procfs_entry("maps", PROCFS_FILE, 0444, pid_dir);
    entry->read_proc = proc_pid_maps_read;
    entry->flags = PROCFS_DYNAMIC | PROCFS_OWNER_ONLY;
    
    // /proc/[pid]/fd directory
    entry = create_procfs_entry("fd", PROCFS_DIR, 0500, pid_dir);
    entry->flags = PROCFS_DYNAMIC | PROCFS_OWNER_ONLY;
    
    // /proc/[pid]/task directory (for threads)
    entry = create_procfs_entry("task", PROCFS_TASK_DIR, 0555, pid_dir);
    entry->flags = PROCFS_DYNAMIC;
    
    // Personality-specific entries
    if (p->personality == PERSONALITY_LINUX) {
        // /proc/[pid]/stat
        entry = create_procfs_entry("stat", PROCFS_FILE, 0444, pid_dir);
        entry->flags = PROCFS_DYNAMIC;
        
        // /proc/[pid]/statm
        entry = create_procfs_entry("statm", PROCFS_FILE, 0444, pid_dir);
        entry->flags = PROCFS_DYNAMIC;
        
        // /proc/[pid]/environ
        entry = create_procfs_entry("environ", PROCFS_FILE, 0400, pid_dir);
        entry->flags = PROCFS_DYNAMIC | PROCFS_OWNER_ONLY;
        
        // /proc/[pid]/auxv
        entry = create_procfs_entry("auxv", PROCFS_FILE, 0400, pid_dir);
        entry->flags = PROCFS_DYNAMIC | PROCFS_OWNER_ONLY;
        
        // /proc/[pid]/limits
        entry = create_procfs_entry("limits", PROCFS_FILE, 0444, pid_dir);
        entry->flags = PROCFS_DYNAMIC;
        
        // /proc/[pid]/mountinfo
        entry = create_procfs_entry("mountinfo", PROCFS_FILE, 0444, pid_dir);
        entry->flags = PROCFS_DYNAMIC;
        
    } else if (p->personality == PERSONALITY_BSD) {
        // /proc/[pid]/ctl (BSD process control)
        entry = create_procfs_entry("ctl", PROCFS_FILE, 0200, pid_dir);
        entry->flags = PROCFS_DYNAMIC | PROCFS_OWNER_ONLY;
        
        // /proc/[pid]/status (different format for BSD)
        entry = create_procfs_entry("status", PROCFS_FILE, 0444, pid_dir);
        entry->read_proc = proc_pid_status_read;
        entry->flags = PROCFS_DYNAMIC;
        
    } else if (p->personality == PERSONALITY_ILLUMOS) {
        // /proc/[pid]/psinfo (Illumos process info)
        entry = create_procfs_entry("psinfo", PROCFS_FILE, 0444, pid_dir);
        entry->flags = PROCFS_DYNAMIC;
        
        // /proc/[pid]/as (address space)
        entry = create_procfs_entry("as", PROCFS_FILE, 0600, pid_dir);
        entry->flags = PROCFS_DYNAMIC | PROCFS_OWNER_ONLY;
        
        // /proc/[pid]/lwp directory (lightweight processes)
        entry = create_procfs_entry("lwp", PROCFS_DIR, 0555, pid_dir);
        entry->flags = PROCFS_DYNAMIC;
    }
    
    return pid_dir;
}

// =============================================================================
// VFS INTERFACE
// =============================================================================

/**
 * Lookup entry in procfs
 */
procfs_entry_t *procfs_lookup(procfs_entry_t *parent, const char *name) {
    if (!parent || parent->type != PROCFS_DIR)
        return NULL;
    
    // Check static entries
    for (procfs_entry_t *e = parent->children; e; e = e->sibling) {
        if (strcmp(e->name, name) == 0) {
            e->ref_count++;
            return e;
        }
    }
    
    // Check for PID directories
    if (parent == procfs_instances[myproc()->personality].root) {
        int pid = atoi(name);
        if (pid > 0) {
            struct proc *p = find_proc_by_pid(pid);
            if (p) {
                return create_pid_entries(p, parent);
            }
        }
    }
    
    return NULL;
}

/**
 * Read from procfs file
 */
int procfs_read(procfs_entry_t *entry, char *buf, int size, off_t offset) {
    if (!entry || entry->type != PROCFS_FILE)
        return -EISDIR;
    
    if (entry->read_proc) {
        return entry->read_proc(myproc(), buf, size, offset);
    }
    
    return 0;  // Empty file
}

/**
 * Write to procfs file
 */
int procfs_write(procfs_entry_t *entry, const char *buf, int size, off_t offset) {
    if (!entry || entry->type != PROCFS_FILE)
        return -EISDIR;
    
    if (entry->write_proc) {
        return entry->write_proc(myproc(), buf, size, offset);
    }
    
    return -EROFS;  // Read-only by default
}

// =============================================================================
// INITIALIZATION
// =============================================================================

/**
 * Initialize /proc and /sys filesystems
 */
void init_procfs(void) {
    // Initialize /proc for each personality
    for (int i = 0; i < PERSONALITY_MAX; i++) {
        init_procfs_personality(i);
    }
    
    // Initialize /sys for each personality
    for (int i = 0; i < PERSONALITY_MAX; i++) {
        init_sysfs_personality(i);
    }
    
    cprintf("/proc and /sys filesystems initialized\n");
    cprintf("  Personality-aware views created:\n");
    cprintf("    - Linux: Full /proc and /sys hierarchy\n");
    cprintf("    - BSD: /proc with curproc symlink\n");
    cprintf("    - Illumos: /proc with psinfo and lwp\n");
    cprintf("    - POSIX: Minimal /proc interface\n");
}
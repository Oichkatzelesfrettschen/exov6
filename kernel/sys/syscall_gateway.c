/**
 * @file syscall_gateway.c
 * @brief Multi-personality syscall gateway implementation
 * 
 * Universal syscall dispatcher supporting FeuerBird native, POSIX 2024,
 * Linux, and BSD compatibility personalities with optimized fast paths.
 */

#include "syscall_gateway.h"
#include "syscall.h"
#include "syscall_posix2024.h"
#include "proc.h"
#include "defs.h"
#include "x86.h"
#include "memlayout.h"

// =============================================================================
// GLOBAL STATE
// =============================================================================

// Personality configurations
static syscall_personality_config_t personality_configs[PERSONALITY_MAX];
static bool personality_initialized[PERSONALITY_MAX] = {false};

// Gateway statistics
static syscall_stats_t gateway_stats = {0};
static bool syscall_tracing_enabled = false;
static struct spinlock gateway_lock;

// Fast path syscall numbers (most common syscalls)
static const unsigned int fast_path_syscalls[] = {
    SYS_getpid,    // Very fast, no side effects
    SYS_uptime,    // Fast read-only
    // Add more as needed
};
static const unsigned int fast_path_count = sizeof(fast_path_syscalls) / sizeof(fast_path_syscalls[0]);

// =============================================================================
// PERSONALITY DETECTION
// =============================================================================

syscall_personality_t detect_binary_personality(struct file *binary) {
    // Simplified ELF personality detection
    // In full implementation, would parse ELF headers, notes, interpreter
    
    if (!binary) 
        return PERSONALITY_FEUERBIRD;
    
    // For now, default to FeuerBird native
    // Real implementation would check:
    // - ELF interpreter path (/lib64/ld-linux-x86-64.so.2 -> Linux)  
    // - ELF notes (NT_GNU_BUILD_ID, etc.)
    // - Section names (.posix2024 -> POSIX)
    // - Program headers and dynamic tags
    
    return PERSONALITY_FEUERBIRD;
}

int set_process_personality(struct proc *p, syscall_personality_t personality) {
    if (personality >= PERSONALITY_MAX || !personality_initialized[personality])
        return -1;
    
    p->personality = personality;
    return 0;
}

syscall_personality_t get_process_personality(struct proc *p) {
    return p ? p->personality : PERSONALITY_FEUERBIRD;
}

// =============================================================================
// FAST PATH IMPLEMENTATION
// =============================================================================

long syscall_fast_path(unsigned long syscall_nr,
                      unsigned long arg0, unsigned long arg1,
                      unsigned long arg2, struct trapframe *tf) {
    // Check if this is a fast-path syscall
    for (unsigned int i = 0; i < fast_path_count; i++) {
        if (syscall_nr == fast_path_syscalls[i]) {
            gateway_stats.fast_path_hits++;
            
            // Handle common fast syscalls directly
            switch (syscall_nr) {
                case SYS_getpid:
                    return myproc()->pid;
                    
                case SYS_uptime:
                    return ticks;
                    
                // Add more fast cases as needed
                default:
                    break;
            }
        }
    }
    
    // Not a fast path syscall
    return -1;
}

// =============================================================================
// PERSONALITY DISPATCH
// =============================================================================

long syscall_personality_dispatch(syscall_personality_t personality,
                                 unsigned long syscall_nr,
                                 unsigned long arg0, unsigned long arg1,
                                 unsigned long arg2, unsigned long arg3,
                                 unsigned long arg4, unsigned long arg5) {
    const syscall_personality_config_t *config;
    const syscall_entry_t *entry;
    syscall_handler_t handler;
    
    // Get personality configuration
    config = &personality_configs[personality];
    if (!config || !config->syscall_table) {
        return -ENOSYS;
    }
    
    // Bounds check
    if (syscall_nr >= config->max_syscall_nr) {
        return -ENOSYS;
    }
    
    // Find syscall entry
    entry = NULL;
    for (unsigned int i = 0; i < config->table_size; i++) {
        if (config->syscall_table[i].nr == syscall_nr) {
            entry = &config->syscall_table[i];
            break;
        }
    }
    
    if (!entry || !entry->handler) {
        return -ENOSYS;
    }
    
    // Capability check
    if (!syscall_check_capability(myproc(), entry)) {
        return -EPERM;
    }
    
    // Trace syscall if enabled
    if (syscall_tracing_enabled) {
        cprintf("syscall[%s:%d]: %s(%p, %p, %p, %p, %p, %p)\n",
                config->name, myproc()->pid, entry->name,
                arg0, arg1, arg2, arg3, arg4, arg5);
    }
    
    // Call handler
    handler = entry->handler;
    gateway_stats.personality_calls[personality]++;
    
    return handler(arg0, arg1, arg2, arg3, arg4, arg5);
}

// =============================================================================
// MAIN GATEWAY DISPATCH
// =============================================================================

long syscall_gateway_dispatch(unsigned long syscall_nr,
                             unsigned long arg0, unsigned long arg1,
                             unsigned long arg2, unsigned long arg3,
                             unsigned long arg4, unsigned long arg5,
                             struct trapframe *tf) {
    struct proc *curproc = myproc();
    syscall_personality_t personality;
    unsigned int class, number;
    long result;
    uint64_t start_cycles = 0;
    
    gateway_stats.total_calls++;
    
    // Get performance counter for overhead measurement
    if (syscall_tracing_enabled) {
        start_cycles = rdtsc();
    }
    
    // Try fast path first for native FeuerBird syscalls
    result = syscall_fast_path(syscall_nr, arg0, arg1, arg2, tf);
    if (result != -1) {
        return result;
    }
    
    // Decode syscall class and number (XNU-style classed syscalls)
    class = syscall_get_class(syscall_nr);
    number = syscall_get_number(syscall_nr);
    
    // Determine personality
    if (class != 0) {
        // Explicit class specified
        switch (class) {
            case SYSCALL_CLASS_FEUERBIRD:
                personality = PERSONALITY_FEUERBIRD;
                syscall_nr = number;
                break;
            case SYSCALL_CLASS_POSIX:
                personality = PERSONALITY_POSIX2024;
                syscall_nr = number;
                break;
            case SYSCALL_CLASS_LINUX:
                personality = PERSONALITY_LINUX;
                syscall_nr = number;
                break;
            case SYSCALL_CLASS_BSD:
                personality = PERSONALITY_BSD;
                syscall_nr = number;
                break;
            case SYSCALL_CLASS_ILLUMOS:
                personality = PERSONALITY_ILLUMOS;
                syscall_nr = number;
                break;
            default:
                gateway_stats.failed_calls++;
                return -EINVAL;
        }
    } else {
        // Use process personality
        personality = get_process_personality(curproc);
    }
    
    // Validate personality
    if (personality >= PERSONALITY_MAX || !personality_initialized[personality]) {
        gateway_stats.failed_calls++;
        return -ENOSYS;
    }
    
    // Dispatch to personality handler
    result = syscall_personality_dispatch(personality, syscall_nr,
                                        arg0, arg1, arg2, arg3, arg4, arg5);
    
    // Track translation overhead
    if (syscall_tracing_enabled && start_cycles != 0) {
        uint64_t end_cycles = rdtsc();
        gateway_stats.translation_overhead += (end_cycles - start_cycles);
    }
    
    // Handle special return cases
    if (result < 0) {
        // Translate error code to personality-specific errno if needed
        const syscall_personality_config_t *config = &personality_configs[personality];
        if (config->translate_errno) {
            result = config->translate_errno((int)result);
        }
        gateway_stats.failed_calls++;
    }
    
    return result;
}

// =============================================================================
// PERSONALITY REGISTRATION
// =============================================================================

void syscall_gateway_init(void) {
    initlock(&gateway_lock, "syscall_gateway");
    
    // Initialize FeuerBird native personality
    memset(&personality_configs[PERSONALITY_FEUERBIRD], 0, 
           sizeof(syscall_personality_config_t));
    personality_configs[PERSONALITY_FEUERBIRD].name = "feuerbird";
    // FeuerBird syscalls use existing dispatch mechanism
    personality_initialized[PERSONALITY_FEUERBIRD] = true;
    
    cprintf("syscall_gateway: Multi-personality syscall gateway initialized\n");
}

int syscall_register_personality(syscall_personality_t personality,
                                const syscall_personality_config_t *config) {
    if (personality >= PERSONALITY_MAX || !config) {
        return -EINVAL;
    }
    
    acquire(&gateway_lock);
    
    // Copy configuration
    personality_configs[personality] = *config;
    personality_initialized[personality] = true;
    
    release(&gateway_lock);
    
    cprintf("syscall_gateway: Registered %s personality (%d syscalls)\n",
            config->name, config->table_size);
    
    return 0;
}

const syscall_personality_config_t *syscall_get_personality_config(
    syscall_personality_t personality) {
    if (personality >= PERSONALITY_MAX || !personality_initialized[personality]) {
        return NULL;
    }
    
    return &personality_configs[personality];
}

// =============================================================================
// DEBUGGING AND STATISTICS
// =============================================================================

void syscall_get_stats(syscall_stats_t *stats) {
    if (stats) {
        acquire(&gateway_lock);
        *stats = gateway_stats;
        release(&gateway_lock);
    }
}

void syscall_reset_stats(void) {
    acquire(&gateway_lock);
    memset(&gateway_stats, 0, sizeof(gateway_stats));
    release(&gateway_lock);
}

void syscall_set_trace(bool enabled) {
    syscall_tracing_enabled = enabled;
    cprintf("syscall_gateway: Tracing %s\n", enabled ? "enabled" : "disabled");
}

// =============================================================================
// POSIX 2024 PERSONALITY INITIALIZATION
// =============================================================================

// POSIX flag translation functions
static int posix_translate_open_flags(int flags) {
    // Already implemented in syscall_posix2024.c
    return translate_posix_open_flags(flags);
}

static int posix_translate_errno(int native_errno) {
    // Simple 1:1 mapping for now, enhance as needed
    return native_errno;
}

// Initialize POSIX 2024 personality
static void init_posix2024_personality(void) {
    syscall_personality_config_t posix_config = {
        .name = "posix2024",
        .syscall_table = (const syscall_entry_t *)posix_syscall_table,
        .max_syscall_nr = POSIX_SYS_MAX,
        .table_size = posix_syscall_table_size,
        .translate_open_flags = posix_translate_open_flags,
        .translate_errno = posix_translate_errno,
        // Other translators would be added here
    };
    
    syscall_register_personality(PERSONALITY_POSIX2024, &posix_config);
}

// =============================================================================
// LATE INITIALIZATION
// =============================================================================

// External personality initialization functions
extern void illumos_personality_init(void);
extern void linux_personality_init(void);
extern void bsd_personality_init(void);

// Initialize all personalities (called after kernel subsystems are ready)
void syscall_gateway_init_personalities(void) {
    // Initialize POSIX 2024 personality
    init_posix2024_personality();
    
    // Initialize Illumos personality
    illumos_personality_init();
    
    // Initialize Linux personality
    linux_personality_init();
    
    // Initialize BSD personality
    bsd_personality_init();
    
    cprintf("syscall_gateway: All personalities initialized\n");
    cprintf("  - FeuerBird native: ✓\n");
    cprintf("  - POSIX 2024: ✓\n");
    cprintf("  - Linux: ✓\n");
    cprintf("  - BSD: ✓\n");
    cprintf("  - Illumos: ✓\n");
}
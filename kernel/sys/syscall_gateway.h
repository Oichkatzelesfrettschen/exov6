/**
 * @file syscall_gateway.h  
 * @brief Multi-personality syscall gateway for universal compatibility
 * 
 * Provides unified syscall dispatch supporting multiple ABI personalities:
 * - FeuerBird native (exokernel optimized)
 * - POSIX 2024 compatibility
 * - Linux compatibility 
 * - BSD compatibility
 * 
 * Based on illumos brand architecture and XNU classed syscalls.
 */

#pragma once

#include <stdint.h>
#include <stdbool.h>
#include "types.h"
#include "trapframe.h"

// =============================================================================
// SYSCALL PERSONALITY TYPES
// =============================================================================

typedef enum {
    PERSONALITY_FEUERBIRD = 0,    // Native exokernel syscalls
    PERSONALITY_POSIX2024 = 1,    // POSIX.1-2024 compatibility
    PERSONALITY_LINUX     = 2,    // Linux syscall compatibility
    PERSONALITY_BSD       = 3,    // BSD syscall compatibility
    PERSONALITY_ILLUMOS   = 4,    // Illumos/Solaris compatibility
    PERSONALITY_MAX       = 5
} syscall_personality_t;

// Syscall class bits (XNU-style)
#define SYSCALL_CLASS_MASK      0xFF000000
#define SYSCALL_CLASS_SHIFT     24
#define SYSCALL_NUMBER_MASK     0x00FFFFFF

#define SYSCALL_CLASS_FEUERBIRD 0x00    // Native exokernel class
#define SYSCALL_CLASS_POSIX     0x01    // POSIX compatibility class  
#define SYSCALL_CLASS_LINUX     0x02    // Linux compatibility class
#define SYSCALL_CLASS_BSD       0x03    // BSD compatibility class
#define SYSCALL_CLASS_ILLUMOS   0x04    // Illumos/Solaris compatibility class

// =============================================================================
// PERSONALITY DETECTION
// =============================================================================

/**
 * Detect binary personality from ELF metadata
 */
syscall_personality_t detect_binary_personality(struct file *binary);

/**
 * Set process personality (can be overridden)
 */
int set_process_personality(struct proc *p, syscall_personality_t personality);

/**
 * Get current process personality
 */
syscall_personality_t get_process_personality(struct proc *p);

// =============================================================================
// SYSCALL HANDLER TYPES
// =============================================================================

// Generic syscall handler signature
typedef long (*syscall_handler_t)(unsigned long arg0, unsigned long arg1,
                                 unsigned long arg2, unsigned long arg3,
                                 unsigned long arg4, unsigned long arg5);

// Syscall entry structure
typedef struct syscall_entry {
    unsigned int nr;            // Syscall number
    const char *name;           // Syscall name (for debugging)
    syscall_handler_t handler;  // Handler function
    unsigned int nargs;         // Number of arguments
    unsigned int flags;         // Syscall flags
} syscall_entry_t;

// Syscall flags
#define SYSCALL_FLAG_NONE       0x00
#define SYSCALL_FLAG_NORETURN   0x01    // Syscall never returns (e.g., exit)
#define SYSCALL_FLAG_RESTARTABLE 0x02   // Can be restarted after signal
#define SYSCALL_FLAG_CAPABILITY 0x04    // Requires capability check

// =============================================================================
// PERSONALITY CONFIGURATION
// =============================================================================

typedef struct syscall_personality_config {
    const char *name;                    // Personality name
    const syscall_entry_t *syscall_table;  // Syscall table
    unsigned int max_syscall_nr;         // Maximum syscall number
    unsigned int table_size;             // Table size
    
    // Structure translators
    int (*translate_stat)(void *src, void *dst, int direction);
    int (*translate_timeval)(void *src, void *dst, int direction);
    int (*translate_sigaction)(void *src, void *dst, int direction);
    
    // Flag mappers
    int (*translate_open_flags)(int flags);
    int (*translate_mmap_prot)(int prot);
    int (*translate_mmap_flags)(int flags);
    
    // Error code mapper
    int (*translate_errno)(int native_errno);
    
} syscall_personality_config_t;

// Translation directions
#define TRANSLATE_TO_NATIVE     0
#define TRANSLATE_FROM_NATIVE   1

// =============================================================================
// GATEWAY DISPATCH FUNCTIONS
// =============================================================================

/**
 * Main syscall gateway entry point
 * Called from trap handler with syscall number and arguments
 */
long syscall_gateway_dispatch(unsigned long syscall_nr, 
                             unsigned long arg0, unsigned long arg1,
                             unsigned long arg2, unsigned long arg3, 
                             unsigned long arg4, unsigned long arg5,
                             struct trapframe *tf);

/**
 * Fast path for common syscalls (bypasses personality layer)
 */
long syscall_fast_path(unsigned long syscall_nr,
                      unsigned long arg0, unsigned long arg1,
                      unsigned long arg2, struct trapframe *tf);

/**
 * Dispatch to specific personality handler
 */
long syscall_personality_dispatch(syscall_personality_t personality,
                                 unsigned long syscall_nr,
                                 unsigned long arg0, unsigned long arg1,
                                 unsigned long arg2, unsigned long arg3,
                                 unsigned long arg4, unsigned long arg5);

// =============================================================================
// PERSONALITY INITIALIZATION
// =============================================================================

/**
 * Initialize syscall gateway system
 */
void syscall_gateway_init(void);

/**
 * Register personality configuration
 */
int syscall_register_personality(syscall_personality_t personality,
                                const syscall_personality_config_t *config);

/**
 * Get personality configuration
 */
const syscall_personality_config_t *syscall_get_personality_config(
    syscall_personality_t personality);

// =============================================================================
// DEBUGGING AND STATISTICS  
// =============================================================================

typedef struct syscall_stats {
    uint64_t total_calls;           // Total syscalls dispatched
    uint64_t fast_path_hits;        // Fast path usage
    uint64_t personality_calls[PERSONALITY_MAX];  // Per-personality counts
    uint64_t translation_overhead;  // Cycles spent in translation
    uint64_t failed_calls;          // Failed syscalls
} syscall_stats_t;

/**
 * Get syscall statistics
 */
void syscall_get_stats(syscall_stats_t *stats);

/**
 * Reset syscall statistics
 */
void syscall_reset_stats(void);

/**
 * Enable/disable syscall tracing
 */
void syscall_set_trace(bool enabled);

// =============================================================================
// EXTERNAL PERSONALITY TABLE DECLARATIONS
// =============================================================================

// FeuerBird native syscalls (from syscall.c)
extern const syscall_entry_t feuerbird_syscall_table[];
extern const unsigned int feuerbird_syscall_table_size;

// POSIX 2024 syscalls (from syscall_posix2024.c)
extern const syscall_entry_t posix_syscall_table[];
extern const unsigned int posix_syscall_table_size;

// Linux compatibility syscalls (to be implemented)
extern const syscall_entry_t linux_syscall_table[];
extern const unsigned int linux_syscall_table_size;

// BSD compatibility syscalls (to be implemented)  
extern const syscall_entry_t bsd_syscall_table[];
extern const unsigned int bsd_syscall_table_size;

// =============================================================================
// INLINE HELPERS
// =============================================================================

/**
 * Extract syscall class from XNU-style classed syscall number
 */
static inline unsigned int syscall_get_class(unsigned long syscall_nr) {
    return (syscall_nr & SYSCALL_CLASS_MASK) >> SYSCALL_CLASS_SHIFT;
}

/**
 * Extract syscall number from classed syscall number
 */
static inline unsigned int syscall_get_number(unsigned long syscall_nr) {
    return syscall_nr & SYSCALL_NUMBER_MASK;
}

/**
 * Create classed syscall number
 */
static inline unsigned long syscall_make_classed(unsigned int class, 
                                                unsigned int number) {
    return ((unsigned long)class << SYSCALL_CLASS_SHIFT) | number;
}

/**
 * Check if process has required capability for syscall
 */
static inline bool syscall_check_capability(struct proc *p, 
                                           const syscall_entry_t *entry) {
    if (!(entry->flags & SYSCALL_FLAG_CAPABILITY))
        return true;  // No capability required
    
    // Check process capabilities (simplified)
    return p->capabilities != 0;  // Would check specific capability
}

#endif // SYSCALL_GATEWAY_H
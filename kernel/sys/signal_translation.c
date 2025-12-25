/**
 * @file signal_translation.c
 * @brief Signal translation between UNIX personalities
 * 
 * Handles signal number translation, semantics differences, and
 * personality-specific signal features across different UNIX variants.
 */

#include "types.h"
#include "defs.h"
#include "param.h"
#include "proc.h"
#include "syscall_gateway.h"
#include "abi_versioning.h"

// =============================================================================
// SIGNAL NUMBER DEFINITIONS
// =============================================================================

// POSIX standard signals (baseline)
#define POSIX_SIGHUP     1
#define POSIX_SIGINT     2
#define POSIX_SIGQUIT    3
#define POSIX_SIGILL     4
#define POSIX_SIGTRAP    5
#define POSIX_SIGABRT    6
#define POSIX_SIGBUS     7
#define POSIX_SIGFPE     8
#define POSIX_SIGKILL    9
#define POSIX_SIGUSR1    10
#define POSIX_SIGSEGV    11
#define POSIX_SIGUSR2    12
#define POSIX_SIGPIPE    13
#define POSIX_SIGALRM    14
#define POSIX_SIGTERM    15
#define POSIX_SIGCHLD    17
#define POSIX_SIGCONT    18
#define POSIX_SIGSTOP    19
#define POSIX_SIGTSTP    20
#define POSIX_SIGTTIN    21
#define POSIX_SIGTTOU    22
#define POSIX_SIGURG     23
#define POSIX_SIGXCPU    24
#define POSIX_SIGXFSZ    25
#define POSIX_SIGVTALRM  26
#define POSIX_SIGPROF    27
#define POSIX_SIGWINCH   28
#define POSIX_SIGIO      29
#define POSIX_SIGPWR     30
#define POSIX_SIGSYS     31

// Linux-specific signals
#define LINUX_SIGHUP     1
#define LINUX_SIGINT     2
#define LINUX_SIGQUIT    3
#define LINUX_SIGILL     4
#define LINUX_SIGTRAP    5
#define LINUX_SIGABRT    6   // Also SIGIOT
#define LINUX_SIGBUS     7
#define LINUX_SIGFPE     8
#define LINUX_SIGKILL    9
#define LINUX_SIGUSR1    10
#define LINUX_SIGSEGV    11
#define LINUX_SIGUSR2    12
#define LINUX_SIGPIPE    13
#define LINUX_SIGALRM    14
#define LINUX_SIGTERM    15
#define LINUX_SIGSTKFLT  16  // Stack fault (x86)
#define LINUX_SIGCHLD    17  // Also SIGCLD
#define LINUX_SIGCONT    18
#define LINUX_SIGSTOP    19
#define LINUX_SIGTSTP    20
#define LINUX_SIGTTIN    21
#define LINUX_SIGTTOU    22
#define LINUX_SIGURG     23
#define LINUX_SIGXCPU    24
#define LINUX_SIGXFSZ    25
#define LINUX_SIGVTALRM  26
#define LINUX_SIGPROF    27
#define LINUX_SIGWINCH   28
#define LINUX_SIGIO      29  // Also SIGPOLL
#define LINUX_SIGPWR     30
#define LINUX_SIGSYS     31
// Real-time signals
#define LINUX_SIGRTMIN   32
#define LINUX_SIGRTMAX   64

// BSD signals (FreeBSD/NetBSD/OpenBSD variations)
#define BSD_SIGHUP       1
#define BSD_SIGINT       2
#define BSD_SIGQUIT      3
#define BSD_SIGILL       4
#define BSD_SIGTRAP      5
#define BSD_SIGABRT      6   // SIGIOT
#define BSD_SIGEMT       7   // Emulator trap
#define BSD_SIGFPE       8
#define BSD_SIGKILL      9
#define BSD_SIGBUS       10  // Different from Linux!
#define BSD_SIGSEGV      11
#define BSD_SIGSYS       12  // Different from Linux!
#define BSD_SIGPIPE      13
#define BSD_SIGALRM      14
#define BSD_SIGTERM      15
#define BSD_SIGURG       16  // Different from Linux!
#define BSD_SIGSTOP      17  // Different from Linux!
#define BSD_SIGTSTP      18  // Different from Linux!
#define BSD_SIGCONT      19  // Different from Linux!
#define BSD_SIGCHLD      20  // Different from Linux!
#define BSD_SIGTTIN      21
#define BSD_SIGTTOU      22
#define BSD_SIGIO        23  // Different from Linux!
#define BSD_SIGXCPU      24
#define BSD_SIGXFSZ      25
#define BSD_SIGVTALRM    26
#define BSD_SIGPROF      27
#define BSD_SIGWINCH     28
#define BSD_SIGINFO      29  // BSD-specific
#define BSD_SIGUSR1      30  // Different from Linux!
#define BSD_SIGUSR2      31  // Different from Linux!
#define BSD_SIGTHR       32  // Thread library signal

// Illumos/Solaris signals
#define ILLUMOS_SIGHUP    1
#define ILLUMOS_SIGINT    2
#define ILLUMOS_SIGQUIT   3
#define ILLUMOS_SIGILL    4
#define ILLUMOS_SIGTRAP   5
#define ILLUMOS_SIGABRT   6   // SIGIOT
#define ILLUMOS_SIGEMT    7   // Emulator trap
#define ILLUMOS_SIGFPE    8
#define ILLUMOS_SIGKILL   9
#define ILLUMOS_SIGBUS    10
#define ILLUMOS_SIGSEGV   11
#define ILLUMOS_SIGSYS    12
#define ILLUMOS_SIGPIPE   13
#define ILLUMOS_SIGALRM   14
#define ILLUMOS_SIGTERM   15
#define ILLUMOS_SIGUSR1   16  // Different from Linux/BSD!
#define ILLUMOS_SIGUSR2   17  // Different from Linux/BSD!
#define ILLUMOS_SIGCHLD   18  // Also SIGCLD
#define ILLUMOS_SIGPWR    19  // Different from Linux!
#define ILLUMOS_SIGWINCH  20  // Different from Linux/BSD!
#define ILLUMOS_SIGURG    21  // Different from Linux/BSD!
#define ILLUMOS_SIGIO     22  // Also SIGPOLL
#define ILLUMOS_SIGSTOP   23  // Different from Linux/BSD!
#define ILLUMOS_SIGTSTP   24  // Different from Linux/BSD!
#define ILLUMOS_SIGCONT   25  // Different from Linux/BSD!
#define ILLUMOS_SIGTTIN   26  // Different from Linux/BSD!
#define ILLUMOS_SIGTTOU   27  // Different from Linux/BSD!
#define ILLUMOS_SIGVTALRM 28
#define ILLUMOS_SIGPROF   29
#define ILLUMOS_SIGXCPU   30
#define ILLUMOS_SIGXFSZ   31
#define ILLUMOS_SIGWAITING 32 // LWP wait
#define ILLUMOS_SIGLWP    33  // LWP signal
#define ILLUMOS_SIGFREEZE 34  // Checkpoint freeze
#define ILLUMOS_SIGTHAW   35  // Checkpoint thaw
#define ILLUMOS_SIGCANCEL 36  // Thread cancellation
#define ILLUMOS_SIGLOST   37  // Resource lost

// V6/V7 UNIX signals (historical)
#define V6_SIGHUP   1
#define V6_SIGINT   2
#define V6_SIGQUIT  3
#define V6_SIGILL   4
#define V6_SIGTRAP  5
#define V6_SIGIOT   6   // Later became SIGABRT
#define V6_SIGEMT   7   // Emulator trap
#define V6_SIGFPE   8
#define V6_SIGKILL  9
#define V6_SIGBUS   10
#define V6_SIGSEGV  11
#define V6_SIGSYS   12
#define V6_SIGPIPE  13
#define V6_SIGALRM  14
#define V6_SIGTERM  15
// V7 added:
#define V7_SIGSTOP  17
#define V7_SIGTSTP  18
#define V7_SIGCONT  19
#define V7_SIGCHLD  20
#define V7_SIGTTIN  21
#define V7_SIGTTOU  22

// =============================================================================
// SIGNAL TRANSLATION TABLES
// =============================================================================

/**
 * Signal translation table entry
 */
typedef struct {
    int posix_sig;
    int linux_sig;
    int bsd_sig;
    int illumos_sig;
    int v6_sig;
    const char *name;
    uint32_t flags;
} signal_translation_t;

// Flags for signal behavior
#define SIG_FLAG_IGNORE_DEFAULT  (1 << 0)  // Can be ignored by default
#define SIG_FLAG_CATCH_DEFAULT   (1 << 1)  // Can be caught by default
#define SIG_FLAG_CORE_DUMP       (1 << 2)  // Generates core dump
#define SIG_FLAG_STOP_PROCESS    (1 << 3)  // Stops process
#define SIG_FLAG_CONTINUE        (1 << 4)  // Continues stopped process
#define SIG_FLAG_REALTIME        (1 << 5)  // Real-time signal
#define SIG_FLAG_THREAD          (1 << 6)  // Thread-specific

// Master signal translation table
static const signal_translation_t signal_table[] = {
    // Standard POSIX signals
    {POSIX_SIGHUP,  LINUX_SIGHUP,  BSD_SIGHUP,  ILLUMOS_SIGHUP,  V6_SIGHUP,  "SIGHUP",  SIG_FLAG_CATCH_DEFAULT},
    {POSIX_SIGINT,  LINUX_SIGINT,  BSD_SIGINT,  ILLUMOS_SIGINT,  V6_SIGINT,  "SIGINT",  SIG_FLAG_CATCH_DEFAULT},
    {POSIX_SIGQUIT, LINUX_SIGQUIT, BSD_SIGQUIT, ILLUMOS_SIGQUIT, V6_SIGQUIT, "SIGQUIT", SIG_FLAG_CATCH_DEFAULT | SIG_FLAG_CORE_DUMP},
    {POSIX_SIGILL,  LINUX_SIGILL,  BSD_SIGILL,  ILLUMOS_SIGILL,  V6_SIGILL,  "SIGILL",  SIG_FLAG_CORE_DUMP},
    {POSIX_SIGTRAP, LINUX_SIGTRAP, BSD_SIGTRAP, ILLUMOS_SIGTRAP, V6_SIGTRAP, "SIGTRAP", SIG_FLAG_CORE_DUMP},
    {POSIX_SIGABRT, LINUX_SIGABRT, BSD_SIGABRT, ILLUMOS_SIGABRT, V6_SIGIOT,  "SIGABRT", SIG_FLAG_CORE_DUMP},
    {POSIX_SIGBUS,  LINUX_SIGBUS,  BSD_SIGBUS,  ILLUMOS_SIGBUS,  V6_SIGBUS,  "SIGBUS",  SIG_FLAG_CORE_DUMP},
    {POSIX_SIGFPE,  LINUX_SIGFPE,  BSD_SIGFPE,  ILLUMOS_SIGFPE,  V6_SIGFPE,  "SIGFPE",  SIG_FLAG_CORE_DUMP},
    {POSIX_SIGKILL, LINUX_SIGKILL, BSD_SIGKILL, ILLUMOS_SIGKILL, V6_SIGKILL, "SIGKILL", 0},  // Cannot be caught
    {POSIX_SIGUSR1, LINUX_SIGUSR1, BSD_SIGUSR1, ILLUMOS_SIGUSR1, 0,          "SIGUSR1", SIG_FLAG_CATCH_DEFAULT},
    {POSIX_SIGSEGV, LINUX_SIGSEGV, BSD_SIGSEGV, ILLUMOS_SIGSEGV, V6_SIGSEGV, "SIGSEGV", SIG_FLAG_CORE_DUMP},
    {POSIX_SIGUSR2, LINUX_SIGUSR2, BSD_SIGUSR2, ILLUMOS_SIGUSR2, 0,          "SIGUSR2", SIG_FLAG_CATCH_DEFAULT},
    {POSIX_SIGPIPE, LINUX_SIGPIPE, BSD_SIGPIPE, ILLUMOS_SIGPIPE, V6_SIGPIPE, "SIGPIPE", SIG_FLAG_CATCH_DEFAULT},
    {POSIX_SIGALRM, LINUX_SIGALRM, BSD_SIGALRM, ILLUMOS_SIGALRM, V6_SIGALRM, "SIGALRM", SIG_FLAG_CATCH_DEFAULT},
    {POSIX_SIGTERM, LINUX_SIGTERM, BSD_SIGTERM, ILLUMOS_SIGTERM, V6_SIGTERM, "SIGTERM", SIG_FLAG_CATCH_DEFAULT},
    
    // Job control signals (added in V7/BSD)
    {POSIX_SIGCHLD, LINUX_SIGCHLD, BSD_SIGCHLD, ILLUMOS_SIGCHLD, V7_SIGCHLD, "SIGCHLD", SIG_FLAG_IGNORE_DEFAULT},
    {POSIX_SIGCONT, LINUX_SIGCONT, BSD_SIGCONT, ILLUMOS_SIGCONT, V7_SIGCONT, "SIGCONT", SIG_FLAG_CONTINUE},
    {POSIX_SIGSTOP, LINUX_SIGSTOP, BSD_SIGSTOP, ILLUMOS_SIGSTOP, V7_SIGSTOP, "SIGSTOP", SIG_FLAG_STOP_PROCESS},
    {POSIX_SIGTSTP, LINUX_SIGTSTP, BSD_SIGTSTP, ILLUMOS_SIGTSTP, V7_SIGTSTP, "SIGTSTP", SIG_FLAG_STOP_PROCESS | SIG_FLAG_CATCH_DEFAULT},
    {POSIX_SIGTTIN, LINUX_SIGTTIN, BSD_SIGTTIN, ILLUMOS_SIGTTIN, V7_SIGTTIN, "SIGTTIN", SIG_FLAG_STOP_PROCESS | SIG_FLAG_CATCH_DEFAULT},
    {POSIX_SIGTTOU, LINUX_SIGTTOU, BSD_SIGTTOU, ILLUMOS_SIGTTOU, V7_SIGTTOU, "SIGTTOU", SIG_FLAG_STOP_PROCESS | SIG_FLAG_CATCH_DEFAULT},
    
    // Extended signals
    {POSIX_SIGURG,    LINUX_SIGURG,    BSD_SIGURG,    ILLUMOS_SIGURG,    0, "SIGURG",    SIG_FLAG_IGNORE_DEFAULT},
    {POSIX_SIGXCPU,   LINUX_SIGXCPU,   BSD_SIGXCPU,   ILLUMOS_SIGXCPU,   0, "SIGXCPU",   SIG_FLAG_CORE_DUMP},
    {POSIX_SIGXFSZ,   LINUX_SIGXFSZ,   BSD_SIGXFSZ,   ILLUMOS_SIGXFSZ,   0, "SIGXFSZ",   SIG_FLAG_CORE_DUMP},
    {POSIX_SIGVTALRM, LINUX_SIGVTALRM, BSD_SIGVTALRM, ILLUMOS_SIGVTALRM, 0, "SIGVTALRM", SIG_FLAG_CATCH_DEFAULT},
    {POSIX_SIGPROF,   LINUX_SIGPROF,   BSD_SIGPROF,   ILLUMOS_SIGPROF,   0, "SIGPROF",   SIG_FLAG_CATCH_DEFAULT},
    {POSIX_SIGWINCH,  LINUX_SIGWINCH,  BSD_SIGWINCH,  ILLUMOS_SIGWINCH,  0, "SIGWINCH",  SIG_FLAG_IGNORE_DEFAULT},
    {POSIX_SIGIO,     LINUX_SIGIO,     BSD_SIGIO,     ILLUMOS_SIGIO,     0, "SIGIO",     SIG_FLAG_CATCH_DEFAULT},
    {POSIX_SIGPWR,    LINUX_SIGPWR,    0,             ILLUMOS_SIGPWR,    0, "SIGPWR",    SIG_FLAG_CATCH_DEFAULT},
    {POSIX_SIGSYS,    LINUX_SIGSYS,    BSD_SIGSYS,    ILLUMOS_SIGSYS,    V6_SIGSYS, "SIGSYS", SIG_FLAG_CORE_DUMP},
    
    // Personality-specific signals
    {0, LINUX_SIGSTKFLT, 0,          0,                0, "SIGSTKFLT", SIG_FLAG_CATCH_DEFAULT},  // Linux x86
    {0, 0,               BSD_SIGEMT,  ILLUMOS_SIGEMT,   V6_SIGEMT, "SIGEMT", SIG_FLAG_CORE_DUMP},    // BSD/Illumos/V6
    {0, 0,               BSD_SIGINFO, 0,                0, "SIGINFO", SIG_FLAG_IGNORE_DEFAULT},     // BSD
    {0, 0,               BSD_SIGTHR,  0,                0, "SIGTHR",  SIG_FLAG_THREAD},            // BSD threads
    {0, 0,               0,           ILLUMOS_SIGWAITING, 0, "SIGWAITING", SIG_FLAG_IGNORE_DEFAULT}, // Illumos
    {0, 0,               0,           ILLUMOS_SIGLWP,   0, "SIGLWP",  SIG_FLAG_THREAD},           // Illumos LWP
    {0, 0,               0,           ILLUMOS_SIGFREEZE, 0, "SIGFREEZE", SIG_FLAG_STOP_PROCESS},   // Illumos
    {0, 0,               0,           ILLUMOS_SIGTHAW,  0, "SIGTHAW", SIG_FLAG_CONTINUE},         // Illumos
    {0, 0,               0,           ILLUMOS_SIGCANCEL, 0, "SIGCANCEL", SIG_FLAG_THREAD},         // Illumos
    {0, 0,               0,           ILLUMOS_SIGLOST,  0, "SIGLOST", SIG_FLAG_CATCH_DEFAULT},    // Illumos
    
    {-1, -1, -1, -1, -1, NULL, 0}  // End marker
};

// =============================================================================
// SIGNAL TRANSLATION FUNCTIONS
// =============================================================================

/**
 * Translate signal number between personalities
 */
int translate_signal(int signum, syscall_personality_t from, syscall_personality_t to) {
    // Fast path: same personality
    if (from == to)
        return signum;
    
    // Find signal in source personality
    int source_sig = -1;
    int target_sig = -1;
    
    for (int i = 0; signal_table[i].name != NULL; i++) {
        const signal_translation_t *entry = &signal_table[i];
        
        // Find matching source signal
        switch (from) {
            case PERSONALITY_POSIX2024:
            case PERSONALITY_FEUERBIRD:
                if (entry->posix_sig == signum)
                    source_sig = i;
                break;
            case PERSONALITY_LINUX:
                if (entry->linux_sig == signum)
                    source_sig = i;
                break;
            case PERSONALITY_BSD:
                if (entry->bsd_sig == signum)
                    source_sig = i;
                break;
            case PERSONALITY_ILLUMOS:
                if (entry->illumos_sig == signum)
                    source_sig = i;
                break;
        }
        
        if (source_sig >= 0)
            break;
    }
    
    if (source_sig < 0) {
        // Unknown signal, return as-is
        return signum;
    }
    
    // Translate to target personality
    const signal_translation_t *entry = &signal_table[source_sig];
    
    switch (to) {
        case PERSONALITY_POSIX2024:
        case PERSONALITY_FEUERBIRD:
            target_sig = entry->posix_sig;
            break;
        case PERSONALITY_LINUX:
            target_sig = entry->linux_sig;
            break;
        case PERSONALITY_BSD:
            target_sig = entry->bsd_sig;
            break;
        case PERSONALITY_ILLUMOS:
            target_sig = entry->illumos_sig;
            break;
    }
    
    // Return translated signal or original if no translation
    return (target_sig > 0) ? target_sig : signum;
}

/**
 * Get signal name for personality
 */
const char *get_signal_name_for_personality(int signum, syscall_personality_t personality) {
    for (int i = 0; signal_table[i].name != NULL; i++) {
        const signal_translation_t *entry = &signal_table[i];
        
        switch (personality) {
            case PERSONALITY_POSIX2024:
            case PERSONALITY_FEUERBIRD:
                if (entry->posix_sig == signum)
                    return entry->name;
                break;
            case PERSONALITY_LINUX:
                if (entry->linux_sig == signum) {
                    // Check for Linux real-time signals
                    if (signum >= LINUX_SIGRTMIN && signum <= LINUX_SIGRTMAX) {
                        static char rtname[32];
                        snprintf(rtname, sizeof(rtname), "SIGRT%d", signum - LINUX_SIGRTMIN);
                        return rtname;
                    }
                    return entry->name;
                }
                break;
            case PERSONALITY_BSD:
                if (entry->bsd_sig == signum)
                    return entry->name;
                break;
            case PERSONALITY_ILLUMOS:
                if (entry->illumos_sig == signum)
                    return entry->name;
                break;
        }
    }
    
    return "SIGUNKNOWN";
}

/**
 * Get signal flags
 */
uint32_t get_signal_flags(int signum, syscall_personality_t personality) {
    for (int i = 0; signal_table[i].name != NULL; i++) {
        const signal_translation_t *entry = &signal_table[i];
        
        switch (personality) {
            case PERSONALITY_POSIX2024:
            case PERSONALITY_FEUERBIRD:
                if (entry->posix_sig == signum)
                    return entry->flags;
                break;
            case PERSONALITY_LINUX:
                if (entry->linux_sig == signum)
                    return entry->flags;
                break;
            case PERSONALITY_BSD:
                if (entry->bsd_sig == signum)
                    return entry->flags;
                break;
            case PERSONALITY_ILLUMOS:
                if (entry->illumos_sig == signum)
                    return entry->flags;
                break;
        }
    }
    
    return 0;
}

// =============================================================================
// SIGNAL MASK TRANSLATION
// =============================================================================

/**
 * Translate signal mask between personalities
 */
uint64_t translate_signal_mask(uint64_t mask, syscall_personality_t from, syscall_personality_t to) {
    if (from == to)
        return mask;
    
    uint64_t new_mask = 0;
    
    // Translate each bit in the mask
    for (int sig = 1; sig <= 64; sig++) {
        if (mask & (1ULL << (sig - 1))) {
            int translated = translate_signal(sig, from, to);
            if (translated > 0 && translated <= 64) {
                new_mask |= (1ULL << (translated - 1));
            }
        }
    }
    
    return new_mask;
}

// =============================================================================
// SIGACTION STRUCTURE TRANSLATION
// =============================================================================

/**
 * Linux sigaction structure
 */
struct sigaction_linux {
    union {
        void (*sa_handler)(int);
        void (*sa_sigaction)(int, void *, void *);
    };
    unsigned long sa_flags;
    void (*sa_restorer)(void);
    uint64_t sa_mask;  // sigset_t
};

/**
 * BSD sigaction structure
 */
struct sigaction_bsd {
    union {
        void (*__sa_handler)(int);
        void (*__sa_sigaction)(int, void *, void *);
    } __sigaction_u;
    int sa_flags;
    uint32_t sa_mask;  // sigset_t (different size!)
};

/**
 * Illumos sigaction structure
 */
struct sigaction_illumos {
    int sa_flags;
    union {
        void (*_handler)(int);
        void (*_sigaction)(int, void *, void *);
    } _funcptr;
    uint64_t sa_mask[2];  // Larger sigset_t
};

/**
 * V6/V7 signal structure (simpler)
 */
struct sigvec_v6 {
    void (*sv_handler)(int);
    int sv_mask;
    int sv_flags;
};

/**
 * Translate sigaction structure between personalities
 */
int translate_sigaction(void *src, syscall_personality_t src_pers,
                       void *dst, syscall_personality_t dst_pers) {
    // Native sigaction structure (POSIX)
    struct sigaction {
        void (*sa_handler)(int);
        uint64_t sa_mask;
        int sa_flags;
    } native;
    
    // Convert source to native
    switch (src_pers) {
        case PERSONALITY_LINUX: {
            struct sigaction_linux *linux = src;
            native.sa_handler = linux->sa_handler;
            native.sa_mask = linux->sa_mask;
            native.sa_flags = linux->sa_flags;
            break;
        }
        case PERSONALITY_BSD: {
            struct sigaction_bsd *bsd = src;
            native.sa_handler = bsd->__sigaction_u.__sa_handler;
            native.sa_mask = bsd->sa_mask;
            native.sa_flags = bsd->sa_flags;
            break;
        }
        case PERSONALITY_ILLUMOS: {
            struct sigaction_illumos *illumos = src;
            native.sa_handler = illumos->_funcptr._handler;
            native.sa_mask = illumos->sa_mask[0];  // Use first 64 bits
            native.sa_flags = illumos->sa_flags;
            break;
        }
        default:
            memcpy(&native, src, sizeof(native));
            break;
    }
    
    // Translate signal mask
    native.sa_mask = translate_signal_mask(native.sa_mask, src_pers, dst_pers);
    
    // Translate flags if needed
    if (src_pers != dst_pers) {
        int new_flags = 0;
        
        // Common flags
        if (native.sa_flags & 0x01) new_flags |= 0x01;  // SA_NOCLDSTOP
        if (native.sa_flags & 0x02) new_flags |= 0x02;  // SA_NOCLDWAIT
        if (native.sa_flags & 0x04) new_flags |= 0x04;  // SA_SIGINFO
        if (native.sa_flags & 0x08) new_flags |= 0x08;  // SA_ONSTACK
        if (native.sa_flags & 0x10) new_flags |= 0x10;  // SA_RESTART
        if (native.sa_flags & 0x20) new_flags |= 0x20;  // SA_NODEFER
        if (native.sa_flags & 0x40) new_flags |= 0x40;  // SA_RESETHAND
        
        native.sa_flags = new_flags;
    }
    
    // Convert native to destination
    switch (dst_pers) {
        case PERSONALITY_LINUX: {
            struct sigaction_linux *linux = dst;
            linux->sa_handler = native.sa_handler;
            linux->sa_mask = native.sa_mask;
            linux->sa_flags = native.sa_flags;
            linux->sa_restorer = NULL;
            break;
        }
        case PERSONALITY_BSD: {
            struct sigaction_bsd *bsd = dst;
            bsd->__sigaction_u.__sa_handler = native.sa_handler;
            bsd->sa_mask = native.sa_mask & 0xFFFFFFFF;  // Truncate to 32 bits
            bsd->sa_flags = native.sa_flags;
            break;
        }
        case PERSONALITY_ILLUMOS: {
            struct sigaction_illumos *illumos = dst;
            illumos->_funcptr._handler = native.sa_handler;
            illumos->sa_mask[0] = native.sa_mask;
            illumos->sa_mask[1] = 0;  // Clear upper bits
            illumos->sa_flags = native.sa_flags;
            break;
        }
        default:
            memcpy(dst, &native, sizeof(native));
            break;
    }
    
    return 0;
}

// =============================================================================
// SIGNAL DELIVERY
// =============================================================================

/**
 * Deliver signal to process with personality translation
 */
int deliver_signal_translated(struct proc *target, int signum, 
                             syscall_personality_t sender_personality) {
    // Translate signal number
    int translated_sig = translate_signal(signum, sender_personality, 
                                         target->personality);
    
    // Check if signal is valid for target personality
    uint32_t flags = get_signal_flags(translated_sig, target->personality);
    
    // Handle special signals
    if (translated_sig == SIGKILL || translated_sig == SIGSTOP) {
        // These cannot be caught or ignored
        target->killed = 1;
        return 0;
    }
    
    // Check signal mask
    if (target->signal_mask & (1ULL << (translated_sig - 1))) {
        // Signal is blocked
        target->pending_signals |= (1ULL << (translated_sig - 1));
        return 0;
    }
    
    // Deliver signal
    if (target->signal_handlers[translated_sig - 1]) {
        // Custom handler
        // TODO: Set up signal frame on stack
        cprintf("Delivering signal %s (%d) to process %d (%s personality)\n",
                get_signal_name_for_personality(translated_sig, target->personality),
                translated_sig, target->pid,
                get_personality_name(target->personality));
    } else {
        // Default action
        if (flags & SIG_FLAG_IGNORE_DEFAULT) {
            // Ignore
            return 0;
        } else if (flags & SIG_FLAG_STOP_PROCESS) {
            // Stop process
            target->state = STOPPED;
        } else if (flags & SIG_FLAG_CONTINUE) {
            // Continue process
            if (target->state == STOPPED)
                target->state = RUNNABLE;
        } else if (flags & SIG_FLAG_CORE_DUMP) {
            // Generate core dump and terminate
            // TODO: Generate core dump
            target->killed = 1;
        } else {
            // Terminate
            target->killed = 1;
        }
    }
    
    return 0;
}

// =============================================================================
// REAL-TIME SIGNALS (Linux-specific)
// =============================================================================

/**
 * Handle Linux real-time signals
 */
int handle_realtime_signal(struct proc *p, int signum, void *value) {
    if (p->personality != PERSONALITY_LINUX)
        return -EINVAL;
    
    if (signum < LINUX_SIGRTMIN || signum > LINUX_SIGRTMAX)
        return -EINVAL;
    
    // Real-time signals are queued, not just flagged
    struct rt_signal {
        int signum;
        void *value;
        struct rt_signal *next;
    };
    
    struct rt_signal *rtsig = kalloc();
    if (!rtsig)
        return -ENOMEM;
    
    rtsig->signum = signum;
    rtsig->value = value;
    rtsig->next = p->rt_signals;
    p->rt_signals = rtsig;
    
    // Wake up process if waiting
    if (p->state == SLEEPING)
        p->state = RUNNABLE;
    
    return 0;
}

// =============================================================================
// SIGNAL SYSTEM CALLS
// =============================================================================

/**
 * Universal signal syscall with personality awareness
 */
long sys_signal_translated(int signum, void (*handler)(int)) {
    struct proc *p = myproc();
    
    // Validate signal number for personality
    uint32_t flags = get_signal_flags(signum, p->personality);
    if (flags == 0 && signum != 0) {
        // Invalid signal for this personality
        return -EINVAL;
    }
    
    // Special signals cannot be caught
    if (signum == SIGKILL || signum == SIGSTOP)
        return -EINVAL;
    
    // Store old handler
    void (*old_handler)(int) = p->signal_handlers[signum - 1];
    
    // Set new handler
    p->signal_handlers[signum - 1] = handler;
    
    cprintf("Process %d (%s): signal %s (%d) handler set to %p\n",
            p->pid, get_personality_name(p->personality),
            get_signal_name_for_personality(signum, p->personality),
            signum, handler);
    
    return (long)old_handler;
}

/**
 * Send signal with translation
 */
long sys_kill_translated(pid_t pid, int signum) {
    struct proc *sender = myproc();
    struct proc *target = find_proc_by_pid(pid);
    
    if (!target)
        return -ESRCH;
    
    // Permission check
    if (sender->uid != 0 && sender->uid != target->uid)
        return -EPERM;
    
    // Deliver with translation
    return deliver_signal_translated(target, signum, sender->personality);
}

/**
 * sigaction with personality translation
 */
long sys_sigaction_translated(int signum, void *act, void *oldact) {
    struct proc *p = myproc();
    
    // Validate signal
    if (signum < 1 || signum > 64)
        return -EINVAL;
    
    // Translate sigaction structures based on personality
    struct sigaction native_act, native_oldact;
    
    if (oldact) {
        // Get current action
        native_oldact.sa_handler = p->signal_handlers[signum - 1];
        native_oldact.sa_mask = p->signal_masks[signum - 1];
        native_oldact.sa_flags = p->signal_flags[signum - 1];
        
        // Translate to personality format
        translate_sigaction(&native_oldact, PERSONALITY_FEUERBIRD,
                          oldact, p->personality);
    }
    
    if (act) {
        // Translate from personality format
        translate_sigaction(act, p->personality,
                          &native_act, PERSONALITY_FEUERBIRD);
        
        // Set new action
        p->signal_handlers[signum - 1] = native_act.sa_handler;
        p->signal_masks[signum - 1] = native_act.sa_mask;
        p->signal_flags[signum - 1] = native_act.sa_flags;
    }
    
    return 0;
}

// =============================================================================
// INITIALIZATION
// =============================================================================

/**
 * Initialize signal translation subsystem
 */
void init_signal_translation(void) {
    cprintf("Signal translation subsystem initialized\n");
    cprintf("  Personality signal mappings loaded:\n");
    cprintf("    - POSIX/FeuerBird: Standard numbering\n");
    cprintf("    - Linux: With real-time signals (32-64)\n");
    cprintf("    - BSD: Different numbering for SIGUSR1/2, job control\n");
    cprintf("    - Illumos: Solaris numbering with LWP signals\n");
    cprintf("    - V6/V7: Historical 15-signal set\n");
    
    // Verify translation table consistency
    int errors = 0;
    for (int i = 0; signal_table[i].name != NULL; i++) {
        const signal_translation_t *entry = &signal_table[i];
        
        // Check for valid signal numbers
        if (entry->posix_sig < 0 || entry->posix_sig > 64) {
            cprintf("WARNING: Invalid POSIX signal %d for %s\n",
                    entry->posix_sig, entry->name);
            errors++;
        }
    }
    
    if (errors > 0) {
        panic("Signal translation table has %d errors", errors);
    }
}
/**
 * @file elf_personality.c
 * @brief Dynamic ELF personality detection
 * 
 * Automatically detects the appropriate syscall personality from
 * ELF headers, interpreter paths, and notes sections.
 */

#include "syscall_gateway.h"
#include "abi_versioning.h"
#include "elf.h"
#include "types.h"
#include "defs.h"
#include "param.h"
#include "memlayout.h"
#include "mmu.h"
#include "proc.h"
#include "fs.h"
#include "file.h"

// =============================================================================
// ELF NOTE DEFINITIONS
// =============================================================================

// Note types for personality detection
#define NT_GNU_ABI_TAG      1
#define NT_GNU_BUILD_ID     3
#define NT_FREEBSD_ABI_TAG  1
#define NT_NETBSD_IDENT     1
#define NT_OPENBSD_IDENT    1
#define NT_SOLARIS_IDENT    1

// ABI tags in notes
#define ELF_NOTE_OS_LINUX       0
#define ELF_NOTE_OS_GNU         1
#define ELF_NOTE_OS_SOLARIS     2
#define ELF_NOTE_OS_FREEBSD     3
#define ELF_NOTE_OS_NETBSD      4
#define ELF_NOTE_OS_OPENBSD     5

// =============================================================================
// INTERPRETER PATHS
// =============================================================================

static const struct {
    const char *path;
    syscall_personality_t personality;
    abi_version_t abi_version;
} interpreter_map[] = {
    // Linux interpreters
    {"/lib64/ld-linux-x86-64.so.2", PERSONALITY_LINUX, ABI_VERSION_LINUX6},
    {"/lib/ld-linux.so.2", PERSONALITY_LINUX, ABI_VERSION_LINUX6},
    {"/lib/ld-musl-x86_64.so.1", PERSONALITY_LINUX, ABI_VERSION_LINUX6},
    
    // FreeBSD interpreters
    {"/libexec/ld-elf.so.1", PERSONALITY_BSD, ABI_VERSION_FBSD14},
    {"/usr/libexec/ld-elf.so.1", PERSONALITY_BSD, ABI_VERSION_FBSD14},
    
    // NetBSD interpreters
    {"/usr/libexec/ld.elf_so", PERSONALITY_BSD, ABI_VERSION_BSD44},
    
    // OpenBSD interpreters
    {"/usr/libexec/ld.so", PERSONALITY_BSD, ABI_VERSION_BSD44},
    
    // Illumos/Solaris interpreters
    {"/usr/lib/ld.so.1", PERSONALITY_ILLUMOS, ABI_VERSION_ILLUMOS},
    {"/lib/ld.so.1", PERSONALITY_ILLUMOS, ABI_VERSION_ILLUMOS},
    
    // Default/Native
    {"/lib/ld-feuerbird.so.1", PERSONALITY_FEUERBIRD, ABI_VERSION_POSIX24},
    
    {NULL, 0, 0}
};

// =============================================================================
// ELF PARSING
// =============================================================================

/**
 * Parse ELF note section for OS identification
 */
static syscall_personality_t parse_elf_notes(struct elfhdr *elf, struct file *f) {
    struct proghdr ph;
    
    // Find PT_NOTE program header
    for (int i = 0; i < elf->phnum; i++) {
        if (readi(f->ip, (char *)&ph, elf->phoff + i * sizeof(ph), sizeof(ph)) != sizeof(ph))
            continue;
        
        if (ph.type != ELF_PROG_NOTE)
            continue;
        
        // Allocate buffer for notes
        char *notes = kalloc();
        if (!notes)
            return PERSONALITY_FEUERBIRD;
        
        // Read notes section
        if (readi(f->ip, notes, ph.off, min(ph.filesz, PGSIZE)) <= 0) {
            kfree(notes);
            continue;
        }
        
        // Parse notes
        char *p = notes;
        char *end = notes + min(ph.filesz, PGSIZE);
        
        while (p < end) {
            struct {
                uint32_t namesz;
                uint32_t descsz;
                uint32_t type;
            } *note = (void *)p;
            
            if (p + sizeof(*note) > end)
                break;
            
            char *name = p + sizeof(*note);
            char *desc = name + ((note->namesz + 3) & ~3);
            
            // Check for GNU ABI tag
            if (note->type == NT_GNU_ABI_TAG && note->namesz >= 4) {
                if (memcmp(name, "GNU\0", 4) == 0) {
                    if (note->descsz >= 16) {
                        uint32_t *abi = (uint32_t *)desc;
                        if (abi[0] == ELF_NOTE_OS_LINUX) {
                            kfree(notes);
                            return PERSONALITY_LINUX;
                        }
                    }
                }
            }
            
            // Check for FreeBSD ABI tag
            if (note->type == NT_FREEBSD_ABI_TAG && note->namesz >= 8) {
                if (memcmp(name, "FreeBSD\0", 8) == 0) {
                    kfree(notes);
                    return PERSONALITY_BSD;
                }
            }
            
            // Check for Solaris ident
            if (note->type == NT_SOLARIS_IDENT && note->namesz >= 8) {
                if (memcmp(name, "Solaris\0", 8) == 0) {
                    kfree(notes);
                    return PERSONALITY_ILLUMOS;
                }
            }
            
            // Move to next note
            p = desc + ((note->descsz + 3) & ~3);
        }
        
        kfree(notes);
    }
    
    return PERSONALITY_FEUERBIRD;  // Default
}

/**
 * Parse ELF interpreter path
 */
static syscall_personality_t parse_elf_interpreter(struct elfhdr *elf, struct file *f) {
    struct proghdr ph;
    
    // Find PT_INTERP program header
    for (int i = 0; i < elf->phnum; i++) {
        if (readi(f->ip, (char *)&ph, elf->phoff + i * sizeof(ph), sizeof(ph)) != sizeof(ph))
            continue;
        
        if (ph.type != ELF_PROG_INTERP)
            continue;
        
        // Read interpreter path
        char interp[256];
        int len = min(ph.filesz, sizeof(interp) - 1);
        
        if (readi(f->ip, interp, ph.off, len) != len)
            continue;
        
        interp[len] = '\0';
        
        // Match against known interpreters
        for (int j = 0; interpreter_map[j].path; j++) {
            if (strcmp(interp, interpreter_map[j].path) == 0) {
                return interpreter_map[j].personality;
            }
        }
    }
    
    return PERSONALITY_FEUERBIRD;  // Default
}

/**
 * Check for Linux-specific sections
 */
static bool has_linux_sections(struct elfhdr *elf, struct file *f) {
    struct {
        uint32_t name;
        uint32_t type;
        uint64_t flags;
        uint64_t addr;
        uint64_t offset;
        uint64_t size;
        uint32_t link;
        uint32_t info;
        uint64_t addralign;
        uint64_t entsize;
    } shdr;
    
    // Look for .gnu.version, .gnu.hash sections
    for (int i = 0; i < elf->shnum; i++) {
        if (readi(f->ip, (char *)&shdr, elf->shoff + i * elf->shentsize, 
                  min(sizeof(shdr), elf->shentsize)) <= 0)
            continue;
        
        // GNU-specific section types
        if (shdr.type == 0x6ffffff6 ||  // SHT_GNU_HASH
            shdr.type == 0x6ffffffe ||  // SHT_GNU_verneed
            shdr.type == 0x6fffffff) {  // SHT_GNU_versym
            return true;
        }
    }
    
    return false;
}

// =============================================================================
// MAIN DETECTION FUNCTION
// =============================================================================

/**
 * Detect personality from ELF binary
 */
syscall_personality_t detect_elf_personality(struct file *f) {
    struct elfhdr elf;
    syscall_personality_t personality;
    
    // Read ELF header
    if (readi(f->ip, (char *)&elf, 0, sizeof(elf)) != sizeof(elf))
        return PERSONALITY_FEUERBIRD;
    
    // Verify ELF magic
    if (elf.magic != ELF_MAGIC)
        return PERSONALITY_FEUERBIRD;
    
    // 1. Try to detect from notes (most reliable)
    personality = parse_elf_notes(&elf, f);
    if (personality != PERSONALITY_FEUERBIRD) {
        cprintf("ELF: Detected personality from notes: %d\n", personality);
        return personality;
    }
    
    // 2. Try to detect from interpreter path
    personality = parse_elf_interpreter(&elf, f);
    if (personality != PERSONALITY_FEUERBIRD) {
        cprintf("ELF: Detected personality from interpreter: %d\n", personality);
        return personality;
    }
    
    // 3. Check for OS-specific sections
    if (has_linux_sections(&elf, f)) {
        cprintf("ELF: Detected Linux from sections\n");
        return PERSONALITY_LINUX;
    }
    
    // 4. Check EI_OSABI field in ELF header
    uint8_t osabi = ((uint8_t *)&elf)[EI_OSABI];
    switch (osabi) {
        case 0:   // ELFOSABI_SYSV
        case 3:   // ELFOSABI_LINUX
            return PERSONALITY_LINUX;
        case 6:   // ELFOSABI_SOLARIS
            return PERSONALITY_ILLUMOS;
        case 9:   // ELFOSABI_FREEBSD
        case 12:  // ELFOSABI_OPENBSD
        case 13:  // ELFOSABI_NETBSD
            return PERSONALITY_BSD;
        default:
            break;
    }
    
    // Default to POSIX personality for unknown ELF files
    cprintf("ELF: No specific personality detected, using POSIX\n");
    return PERSONALITY_POSIX2024;
}

// =============================================================================
// PROCESS PERSONALITY SETUP
// =============================================================================

/**
 * Set up process personality based on binary
 */
int setup_process_personality(struct proc *p, struct file *f) {
    syscall_personality_t personality;
    
    // Detect personality from ELF
    personality = detect_elf_personality(f);
    
    // Set process personality
    p->personality = personality;
    
    // Set up personality-specific defaults
    switch (personality) {
        case PERSONALITY_LINUX:
            // Linux processes expect certain signals and behaviors
            p->signal_mask = 0;
            p->flags |= PROC_LINUX_COMPAT;
            break;
            
        case PERSONALITY_BSD:
            // BSD processes may expect different signal numbers
            p->flags |= PROC_BSD_COMPAT;
            break;
            
        case PERSONALITY_ILLUMOS:
            // Illumos processes may use zones
            p->flags |= PROC_ILLUMOS_COMPAT;
            break;
            
        case PERSONALITY_POSIX2024:
            // POSIX compliance mode
            p->flags |= PROC_POSIX_STRICT;
            break;
            
        case PERSONALITY_FEUERBIRD:
        default:
            // Native mode, no special flags
            break;
    }
    
    cprintf("Process %d: personality set to %d\n", p->pid, personality);
    
    return 0;
}

// =============================================================================
// BRAND MECHANISM (RUNTIME PERSONALITY SWITCHING)
// =============================================================================

/**
 * Switch process personality at runtime (brand mechanism)
 */
int switch_process_personality(struct proc *p, syscall_personality_t new_personality) {
    if (new_personality >= PERSONALITY_MAX)
        return -EINVAL;
    
    // Some personalities cannot be entered after process start
    if (p->state != EMBRYO && new_personality == PERSONALITY_FEUERBIRD) {
        // Cannot switch to native after process has started
        return -EPERM;
    }
    
    // Clear old personality flags
    p->flags &= ~(PROC_LINUX_COMPAT | PROC_BSD_COMPAT | 
                  PROC_ILLUMOS_COMPAT | PROC_POSIX_STRICT);
    
    // Set new personality
    p->personality = new_personality;
    
    // Set new flags
    switch (new_personality) {
        case PERSONALITY_LINUX:
            p->flags |= PROC_LINUX_COMPAT;
            break;
        case PERSONALITY_BSD:
            p->flags |= PROC_BSD_COMPAT;
            break;
        case PERSONALITY_ILLUMOS:
            p->flags |= PROC_ILLUMOS_COMPAT;
            break;
        case PERSONALITY_POSIX2024:
            p->flags |= PROC_POSIX_STRICT;
            break;
        default:
            break;
    }
    
    cprintf("Process %d: personality switched to %d\n", p->pid, new_personality);
    
    return 0;
}

// =============================================================================
// PERSONALITY QUERY
// =============================================================================

/**
 * Get personality name string
 */
const char *get_personality_name(syscall_personality_t personality) {
    static const char *names[] = {
        [PERSONALITY_FEUERBIRD] = "FeuerBird",
        [PERSONALITY_POSIX2024] = "POSIX.1-2024",
        [PERSONALITY_LINUX]     = "Linux",
        [PERSONALITY_BSD]       = "BSD",
        [PERSONALITY_ILLUMOS]   = "Illumos",
    };
    
    if (personality < PERSONALITY_MAX)
        return names[personality];
    
    return "Unknown";
}

/**
 * Get ABI version for personality
 */
abi_version_t get_personality_abi_version(syscall_personality_t personality) {
    switch (personality) {
        case PERSONALITY_LINUX:
            return ABI_VERSION_LINUX6;
        case PERSONALITY_BSD:
            return ABI_VERSION_FBSD14;
        case PERSONALITY_ILLUMOS:
            return ABI_VERSION_ILLUMOS;
        case PERSONALITY_POSIX2024:
            return ABI_VERSION_POSIX24;
        case PERSONALITY_FEUERBIRD:
        default:
            return ABI_VERSION_POSIX24;
    }
}
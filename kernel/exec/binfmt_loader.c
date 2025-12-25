/**
 * @file binfmt_loader.c
 * @brief Binary format loaders for multiple executable formats
 * 
 * Supports: ELF, a.out (V6/V7/BSD), COFF, PE/COFF, Mach-O
 */

#include "types.h"
#include "param.h"
#include "memlayout.h"
#include "mmu.h"
#include "proc.h"
#include "defs.h"
#include "x86.h"
#include "elf.h"
#include "syscall_gateway.h"
#include "abi_versioning.h"

// =============================================================================
// BINARY FORMAT DEFINITIONS
// =============================================================================

// a.out magic numbers
#define AOUT_OMAGIC  0407    // V6/V7 old impure format
#define AOUT_NMAGIC  0410    // V7 read-only text
#define AOUT_ZMAGIC  0413    // Demand paged
#define AOUT_QMAGIC  0314    // QMAGIC (BSD)
#define AOUT_CMAGIC  0421    // Core file

// COFF magic numbers
#define COFF_I386MAGIC    0x14c   // Intel 386
#define COFF_AMD64MAGIC   0x8664  // AMD64
#define COFF_ARMMAGIC     0x1c0   // ARM
#define COFF_ARM64MAGIC   0xaa64  // ARM64

// PE signature
#define PE_SIGNATURE      0x00004550  // "PE\0\0"

// Mach-O magic numbers
#define MH_MAGIC          0xfeedface  // 32-bit
#define MH_MAGIC_64       0xfeedfacf  // 64-bit
#define MH_CIGAM          0xcefaedfe  // Swapped 32-bit
#define MH_CIGAM_64       0xcffaedfe  // Swapped 64-bit

// =============================================================================
// A.OUT FORMAT (V6/V7/BSD)
// =============================================================================

/**
 * V6 a.out header (smallest)
 */
struct exec_v6 {
    uint16_t a_magic;    // Magic number
    uint16_t a_text;     // Text size
    uint16_t a_data;     // Data size
    uint16_t a_bss;      // BSS size
    uint16_t a_syms;     // Symbol table size
    uint16_t a_entry;    // Entry point
    uint16_t a_unused;   // Unused
    uint16_t a_flag;     // Relocation info
};

/**
 * V7/BSD a.out header
 */
struct exec_v7 {
    uint32_t a_magic;    // Magic number
    uint32_t a_text;     // Text segment size
    uint32_t a_data;     // Data segment size
    uint32_t a_bss;      // BSS segment size
    uint32_t a_syms;     // Symbol table size
    uint32_t a_entry;    // Entry point address
    uint32_t a_trsize;   // Text relocation size
    uint32_t a_drsize;   // Data relocation size
};

/**
 * BSD/386BSD a.out header (extended)
 */
struct exec_bsd {
    uint32_t a_midmag;   // Magic and machine ID
    uint32_t a_text;     // Text segment size
    uint32_t a_data;     // Data segment size
    uint32_t a_bss;      // BSS segment size
    uint32_t a_syms;     // Symbol table size
    uint32_t a_entry;    // Entry point
    uint32_t a_trsize;   // Text relocation
    uint32_t a_drsize;   // Data relocation
};

// =============================================================================
// COFF FORMAT (System V)
// =============================================================================

/**
 * COFF file header
 */
struct coff_filehdr {
    uint16_t f_magic;    // Magic number
    uint16_t f_nscns;    // Number of sections
    uint32_t f_timdat;   // Time and date stamp
    uint32_t f_symptr;   // Symbol table pointer
    uint32_t f_nsyms;    // Number of symbols
    uint16_t f_opthdr;   // Optional header size
    uint16_t f_flags;    // Flags
};

/**
 * COFF optional header (a.out format)
 */
struct coff_aouthdr {
    uint16_t magic;      // Magic number
    uint16_t vstamp;     // Version stamp
    uint32_t tsize;      // Text size
    uint32_t dsize;      // Data size
    uint32_t bsize;      // BSS size
    uint32_t entry;      // Entry point
    uint32_t text_start; // Text start address
    uint32_t data_start; // Data start address
};

/**
 * COFF section header
 */
struct coff_scnhdr {
    char s_name[8];      // Section name
    uint32_t s_paddr;    // Physical address
    uint32_t s_vaddr;    // Virtual address
    uint32_t s_size;     // Section size
    uint32_t s_scnptr;   // File pointer to section
    uint32_t s_relptr;   // File pointer to relocation
    uint32_t s_lnnoptr;  // File pointer to line numbers
    uint16_t s_nreloc;   // Number of relocations
    uint16_t s_nlnno;    // Number of line numbers
    uint32_t s_flags;    // Section flags
};

// =============================================================================
// PE/COFF FORMAT (Windows)
// =============================================================================

/**
 * DOS header (for PE files)
 */
struct dos_header {
    uint16_t e_magic;    // Magic number (MZ)
    uint16_t e_cblp;     // Bytes on last page
    uint16_t e_cp;       // Pages in file
    uint16_t e_crlc;     // Relocations
    uint16_t e_cparhdr;  // Size of header
    uint16_t e_minalloc; // Minimum extra paragraphs
    uint16_t e_maxalloc; // Maximum extra paragraphs
    uint16_t e_ss;       // Initial SS
    uint16_t e_sp;       // Initial SP
    uint16_t e_csum;     // Checksum
    uint16_t e_ip;       // Initial IP
    uint16_t e_cs;       // Initial CS
    uint16_t e_lfarlc;   // File address of relocation table
    uint16_t e_ovno;     // Overlay number
    uint16_t e_res[4];   // Reserved
    uint16_t e_oemid;    // OEM identifier
    uint16_t e_oeminfo;  // OEM information
    uint16_t e_res2[10]; // Reserved
    uint32_t e_lfanew;   // File address of PE header
};

/**
 * PE header
 */
struct pe_header {
    uint32_t signature;  // PE signature
    struct coff_filehdr file_header;
    // Followed by optional header
};

// =============================================================================
// MACH-O FORMAT (macOS/Darwin)
// =============================================================================

/**
 * Mach-O header
 */
struct mach_header {
    uint32_t magic;      // Magic number
    uint32_t cputype;    // CPU type
    uint32_t cpusubtype; // CPU subtype
    uint32_t filetype;   // File type
    uint32_t ncmds;      // Number of load commands
    uint32_t sizeofcmds; // Size of load commands
    uint32_t flags;      // Flags
};

/**
 * Mach-O 64-bit header
 */
struct mach_header_64 {
    uint32_t magic;
    uint32_t cputype;
    uint32_t cpusubtype;
    uint32_t filetype;
    uint32_t ncmds;
    uint32_t sizeofcmds;
    uint32_t flags;
    uint32_t reserved;
};

/**
 * Mach-O load command
 */
struct load_command {
    uint32_t cmd;        // Command type
    uint32_t cmdsize;    // Command size
};

// =============================================================================
// BINARY FORMAT DETECTION
// =============================================================================

typedef enum {
    BINFMT_UNKNOWN,
    BINFMT_ELF,
    BINFMT_AOUT_V6,
    BINFMT_AOUT_V7,
    BINFMT_AOUT_BSD,
    BINFMT_COFF,
    BINFMT_PE,
    BINFMT_MACHO,
    BINFMT_MACHO64,
    BINFMT_SCRIPT,      // Shell script with #!
} binary_format_t;

/**
 * Detect binary format from header
 */
binary_format_t detect_binary_format(char *data, int size) {
    if (size < 4)
        return BINFMT_UNKNOWN;
    
    uint32_t magic = *(uint32_t *)data;
    uint16_t magic16 = *(uint16_t *)data;
    
    // Check ELF
    if (magic == ELF_MAGIC)
        return BINFMT_ELF;
    
    // Check Mach-O
    if (magic == MH_MAGIC || magic == MH_CIGAM)
        return BINFMT_MACHO;
    if (magic == MH_MAGIC_64 || magic == MH_CIGAM_64)
        return BINFMT_MACHO64;
    
    // Check PE (look for MZ header)
    if (magic16 == 0x5A4D) {  // "MZ"
        if (size >= sizeof(struct dos_header)) {
            struct dos_header *dos = (struct dos_header *)data;
            if (dos->e_lfanew < size - 4) {
                uint32_t pe_sig = *(uint32_t *)(data + dos->e_lfanew);
                if (pe_sig == PE_SIGNATURE)
                    return BINFMT_PE;
            }
        }
    }
    
    // Check COFF
    if (magic16 == COFF_I386MAGIC || magic16 == COFF_AMD64MAGIC)
        return BINFMT_COFF;
    
    // Check a.out variants
    if (magic16 == AOUT_OMAGIC || magic16 == AOUT_NMAGIC)
        return BINFMT_AOUT_V6;  // V6 uses 16-bit magic
    
    if (magic == AOUT_ZMAGIC || magic == AOUT_QMAGIC)
        return BINFMT_AOUT_BSD;
    
    // Check for V7 a.out (32-bit magic)
    if ((magic & 0xFFFF) == AOUT_OMAGIC || (magic & 0xFFFF) == AOUT_NMAGIC)
        return BINFMT_AOUT_V7;
    
    // Check for script
    if (size >= 2 && data[0] == '#' && data[1] == '!')
        return BINFMT_SCRIPT;
    
    return BINFMT_UNKNOWN;
}

// =============================================================================
// A.OUT LOADER
// =============================================================================

/**
 * Load V6 a.out binary
 */
int load_aout_v6(struct inode *ip, struct proc *p) {
    struct exec_v6 hdr;
    pde_t *pgdir = 0;
    uint sz = 0;
    
    // Read header
    if (readi(ip, (char *)&hdr, 0, sizeof(hdr)) != sizeof(hdr))
        return -1;
    
    // Validate magic
    if (hdr.a_magic != AOUT_OMAGIC && hdr.a_magic != AOUT_NMAGIC)
        return -1;
    
    // V6 uses 16-bit sizes, need to scale up
    uint text_size = hdr.a_text * 2;  // Word to byte
    uint data_size = hdr.a_data * 2;
    uint bss_size = hdr.a_bss * 2;
    
    // Set up memory
    if ((pgdir = setupkvm()) == 0)
        return -1;
    
    // Load text segment
    sz = PGSIZE;  // First page for stack guard
    if ((sz = allocuvm(pgdir, sz, sz + text_size)) == 0)
        goto bad;
    if (loaduvm(pgdir, (char *)PGSIZE, ip, sizeof(hdr), text_size) < 0)
        goto bad;
    
    // Load data segment
    if ((sz = allocuvm(pgdir, sz, sz + data_size)) == 0)
        goto bad;
    if (loaduvm(pgdir, (char *)(PGSIZE + text_size), ip, 
                sizeof(hdr) + text_size, data_size) < 0)
        goto bad;
    
    // Allocate BSS
    if ((sz = allocuvm(pgdir, sz, sz + bss_size)) == 0)
        goto bad;
    
    // Allocate stack
    sz = PGROUNDUP(sz);
    if ((sz = allocuvm(pgdir, sz, sz + 2*PGSIZE)) == 0)
        goto bad;
    clearpteu(pgdir, (char *)(sz - 2*PGSIZE));
    
    // Set up process
    p->sz = sz;
    p->pgdir = pgdir;
    p->tf->eip = hdr.a_entry ? hdr.a_entry : PGSIZE;  // Entry point
    p->tf->esp = sz;
    
    // Set V6 personality
    p->personality = PERSONALITY_POSIX2024;  // Use POSIX for V6
    p->abi_version = ABI_VERSION_V6;
    
    cprintf("Loaded V6 a.out binary (text=%d data=%d bss=%d)\n",
            text_size, data_size, bss_size);
    
    switchuvm(p);
    return 0;
    
bad:
    if (pgdir)
        freevm(pgdir);
    return -1;
}

/**
 * Load V7/BSD a.out binary
 */
int load_aout_v7(struct inode *ip, struct proc *p) {
    struct exec_v7 hdr;
    pde_t *pgdir = 0;
    uint sz = 0;
    
    // Read header
    if (readi(ip, (char *)&hdr, 0, sizeof(hdr)) != sizeof(hdr))
        return -1;
    
    // Validate magic
    uint32_t magic = hdr.a_magic & 0xFFFF;
    if (magic != AOUT_OMAGIC && magic != AOUT_NMAGIC && 
        magic != AOUT_ZMAGIC && magic != AOUT_QMAGIC)
        return -1;
    
    if ((pgdir = setupkvm()) == 0)
        return -1;
    
    // Calculate load address based on magic
    uint load_addr = PGSIZE;
    if (magic == AOUT_ZMAGIC)
        load_addr = 0;  // Demand paged starts at 0
    
    // Load segments
    sz = load_addr;
    
    // Text segment
    if ((sz = allocuvm(pgdir, sz, sz + hdr.a_text)) == 0)
        goto bad;
    if (loaduvm(pgdir, (char *)load_addr, ip, sizeof(hdr), hdr.a_text) < 0)
        goto bad;
    
    // Data segment
    sz = PGROUNDUP(sz);
    uint data_addr = sz;
    if ((sz = allocuvm(pgdir, sz, sz + hdr.a_data)) == 0)
        goto bad;
    if (loaduvm(pgdir, (char *)data_addr, ip, 
                sizeof(hdr) + hdr.a_text, hdr.a_data) < 0)
        goto bad;
    
    // BSS segment
    if ((sz = allocuvm(pgdir, sz, sz + hdr.a_bss)) == 0)
        goto bad;
    
    // Stack
    sz = PGROUNDUP(sz);
    if ((sz = allocuvm(pgdir, sz, sz + 2*PGSIZE)) == 0)
        goto bad;
    clearpteu(pgdir, (char *)(sz - 2*PGSIZE));
    
    // Set up process
    p->sz = sz;
    p->pgdir = pgdir;
    p->tf->eip = hdr.a_entry;
    p->tf->esp = sz;
    
    // Detect personality from magic
    if (magic == AOUT_QMAGIC) {
        p->personality = PERSONALITY_BSD;
        p->abi_version = ABI_VERSION_BSD44;
    } else {
        p->personality = PERSONALITY_POSIX2024;
        p->abi_version = ABI_VERSION_V7;
    }
    
    cprintf("Loaded V7/BSD a.out binary (magic=%x text=%d data=%d bss=%d)\n",
            magic, hdr.a_text, hdr.a_data, hdr.a_bss);
    
    switchuvm(p);
    return 0;
    
bad:
    if (pgdir)
        freevm(pgdir);
    return -1;
}

// =============================================================================
// COFF LOADER
// =============================================================================

/**
 * Load COFF binary
 */
int load_coff(struct inode *ip, struct proc *p) {
    struct coff_filehdr fhdr;
    struct coff_aouthdr ahdr;
    struct coff_scnhdr shdr;
    pde_t *pgdir = 0;
    uint sz = 0;
    
    // Read file header
    if (readi(ip, (char *)&fhdr, 0, sizeof(fhdr)) != sizeof(fhdr))
        return -1;
    
    // Validate magic
    if (fhdr.f_magic != COFF_I386MAGIC && fhdr.f_magic != COFF_AMD64MAGIC)
        return -1;
    
    // Read optional header
    if (fhdr.f_opthdr > 0) {
        if (readi(ip, (char *)&ahdr, sizeof(fhdr), sizeof(ahdr)) != sizeof(ahdr))
            return -1;
    }
    
    if ((pgdir = setupkvm()) == 0)
        return -1;
    
    // Load sections
    uint offset = sizeof(fhdr) + fhdr.f_opthdr;
    sz = PGSIZE;
    
    for (int i = 0; i < fhdr.f_nscns; i++) {
        // Read section header
        if (readi(ip, (char *)&shdr, offset, sizeof(shdr)) != sizeof(shdr))
            goto bad;
        offset += sizeof(shdr);
        
        // Check section name
        if (strncmp(shdr.s_name, ".text", 5) == 0 ||
            strncmp(shdr.s_name, ".data", 5) == 0 ||
            strncmp(shdr.s_name, ".bss", 4) == 0) {
            
            // Allocate memory for section
            uint vaddr = shdr.s_vaddr;
            if (vaddr < sz)
                vaddr = sz;
            
            if ((sz = allocuvm(pgdir, vaddr, vaddr + shdr.s_size)) == 0)
                goto bad;
            
            // Load section data (except BSS)
            if (strncmp(shdr.s_name, ".bss", 4) != 0 && shdr.s_size > 0) {
                if (loaduvm(pgdir, (char *)vaddr, ip, shdr.s_scnptr, shdr.s_size) < 0)
                    goto bad;
            }
        }
    }
    
    // Stack
    sz = PGROUNDUP(sz);
    if ((sz = allocuvm(pgdir, sz, sz + 2*PGSIZE)) == 0)
        goto bad;
    clearpteu(pgdir, (char *)(sz - 2*PGSIZE));
    
    // Set up process
    p->sz = sz;
    p->pgdir = pgdir;
    p->tf->eip = ahdr.entry;
    p->tf->esp = sz;
    
    // COFF usually means System V
    p->personality = PERSONALITY_POSIX2024;
    p->abi_version = ABI_VERSION_SVR4;
    
    cprintf("Loaded COFF binary (sections=%d entry=%x)\n",
            fhdr.f_nscns, ahdr.entry);
    
    switchuvm(p);
    return 0;
    
bad:
    if (pgdir)
        freevm(pgdir);
    return -1;
}

// =============================================================================
// SCRIPT LOADER
// =============================================================================

/**
 * Load shell script with #! interpreter
 */
int load_script(struct inode *ip, struct proc *p, char *path) {
    char buf[128];
    char interp[64];
    char arg[64];
    
    // Read first line
    if (readi(ip, buf, 0, sizeof(buf)) <= 2)
        return -1;
    
    // Must start with #!
    if (buf[0] != '#' || buf[1] != '!')
        return -1;
    
    // Parse interpreter and optional argument
    int i = 2;
    while (i < sizeof(buf) && (buf[i] == ' ' || buf[i] == '\t'))
        i++;
    
    int j = 0;
    while (i < sizeof(buf) && buf[i] != ' ' && buf[i] != '\t' && 
           buf[i] != '\n' && j < sizeof(interp) - 1) {
        interp[j++] = buf[i++];
    }
    interp[j] = '\0';
    
    // Optional argument
    arg[0] = '\0';
    if (buf[i] == ' ' || buf[i] == '\t') {
        while (i < sizeof(buf) && (buf[i] == ' ' || buf[i] == '\t'))
            i++;
        
        j = 0;
        while (i < sizeof(buf) && buf[i] != '\n' && j < sizeof(arg) - 1) {
            arg[j++] = buf[i++];
        }
        arg[j] = '\0';
    }
    
    cprintf("Script interpreter: %s %s %s\n", interp, arg, path);
    
    // Load the interpreter instead
    struct inode *iip = namei(interp);
    if (iip == 0)
        return -1;
    
    // Set up arguments: interp [arg] script [original args]
    // TODO: Properly set up argv with script name
    
    int ret = exec_inode(iip, p);
    iunlock(iip);
    
    return ret;
}

// =============================================================================
// MAIN EXEC FUNCTION
// =============================================================================

/**
 * Execute inode with format detection
 */
int exec_inode(struct inode *ip, struct proc *p) {
    char header[512];
    
    // Read header for format detection
    ilock(ip);
    int n = readi(ip, header, 0, sizeof(header));
    iunlock(ip);
    
    if (n < 4)
        return -1;
    
    // Detect format
    binary_format_t format = detect_binary_format(header, n);
    
    cprintf("Binary format detected: %d\n", format);
    
    // Load based on format
    switch (format) {
        case BINFMT_ELF:
            return exec(ip);  // Use existing ELF loader
            
        case BINFMT_AOUT_V6:
            return load_aout_v6(ip, p);
            
        case BINFMT_AOUT_V7:
        case BINFMT_AOUT_BSD:
            return load_aout_v7(ip, p);
            
        case BINFMT_COFF:
            return load_coff(ip, p);
            
        case BINFMT_PE:
            cprintf("PE/COFF format not yet supported\n");
            return -1;
            
        case BINFMT_MACHO:
        case BINFMT_MACHO64:
            cprintf("Mach-O format not yet supported\n");
            return -1;
            
        case BINFMT_SCRIPT:
            return load_script(ip, p, 0);  // TODO: Pass script path
            
        default:
            cprintf("Unknown binary format\n");
            return -1;
    }
}

// =============================================================================
// INITIALIZATION
// =============================================================================

/**
 * Initialize binary format loader subsystem
 */
void init_binfmt(void) {
    cprintf("Binary format loader initialized\n");
    cprintf("  Supported formats:\n");
    cprintf("    - ELF (32/64-bit)\n");
    cprintf("    - a.out (V6/V7/BSD)\n");
    cprintf("    - COFF (System V)\n");
    cprintf("    - Scripts (#!)\n");
    cprintf("  Planned support:\n");
    cprintf("    - PE/COFF (Windows)\n");
    cprintf("    - Mach-O (macOS)\n");
}
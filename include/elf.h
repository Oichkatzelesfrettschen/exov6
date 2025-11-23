/**
 * @file elf.h
 * @brief ELF64 Executable Format Definitions (Phase 10)
 *
 * This header defines the ELF64 format for loading executables in the
 * exokernel. Following pure exokernel philosophy:
 *
 *   - The KERNEL only provides raw memory allocation (sys_page_alloc)
 *   - The LIBOS parses ELF headers and maps segments
 *   - This decouples format knowledge from the kernel
 *
 * Inspired by:
 *   - MIT Exokernel (Aegis): Kernel exports physical pages, LibOS handles ELF
 *   - seL4: User-space ELF loader with capability-based memory mapping
 *   - MirageOS: Compile-time linking eliminates runtime ELF parsing
 *
 * ELF64 is used for x86_64 and AArch64 targets.
 */

#ifndef ELF_H
#define ELF_H

#include <stdint.h>

/* ═══════════════════════════════════════════════════════════════════════════
 * ELF Magic Number
 * ═══════════════════════════════════════════════════════════════════════════ */

#define ELF_MAGIC       0x464C457FU     /* "\x7FELF" in little endian */

/* ═══════════════════════════════════════════════════════════════════════════
 * ELF Identification (e_ident) indices
 * ═══════════════════════════════════════════════════════════════════════════ */

#define EI_MAG0         0               /* File identification byte 0 */
#define EI_MAG1         1               /* File identification byte 1 */
#define EI_MAG2         2               /* File identification byte 2 */
#define EI_MAG3         3               /* File identification byte 3 */
#define EI_CLASS        4               /* File class */
#define EI_DATA         5               /* Data encoding */
#define EI_VERSION      6               /* File version */
#define EI_OSABI        7               /* OS/ABI identification */
#define EI_ABIVERSION   8               /* ABI version */
#define EI_PAD          9               /* Start of padding bytes */
#define EI_NIDENT       16              /* Size of e_ident[] */

/* EI_CLASS values */
#define ELFCLASSNONE    0               /* Invalid class */
#define ELFCLASS32      1               /* 32-bit objects */
#define ELFCLASS64      2               /* 64-bit objects */

/* EI_DATA values */
#define ELFDATANONE     0               /* Invalid data encoding */
#define ELFDATA2LSB     1               /* Little endian */
#define ELFDATA2MSB     2               /* Big endian */

/* ═══════════════════════════════════════════════════════════════════════════
 * ELF64 File Header
 * ═══════════════════════════════════════════════════════════════════════════ */

typedef struct {
    uint8_t     e_ident[EI_NIDENT];     /* ELF identification */
    uint16_t    e_type;                 /* Object file type */
    uint16_t    e_machine;              /* Machine type */
    uint32_t    e_version;              /* Object file version */
    uint64_t    e_entry;                /* Entry point address */
    uint64_t    e_phoff;                /* Program header offset */
    uint64_t    e_shoff;                /* Section header offset */
    uint32_t    e_flags;                /* Processor-specific flags */
    uint16_t    e_ehsize;               /* ELF header size */
    uint16_t    e_phentsize;            /* Program header entry size */
    uint16_t    e_phnum;                /* Number of program headers */
    uint16_t    e_shentsize;            /* Section header entry size */
    uint16_t    e_shnum;                /* Number of section headers */
    uint16_t    e_shstrndx;             /* Section name string table index */
} Elf64_Ehdr;

/* e_type values */
#define ET_NONE         0               /* No file type */
#define ET_REL          1               /* Relocatable file */
#define ET_EXEC         2               /* Executable file */
#define ET_DYN          3               /* Shared object file */
#define ET_CORE         4               /* Core file */

/* e_machine values (relevant to exov6) */
#define EM_X86_64       62              /* AMD x86-64 */
#define EM_AARCH64      183             /* ARM AArch64 */
#define EM_RISCV        243             /* RISC-V */

/* ═══════════════════════════════════════════════════════════════════════════
 * ELF64 Program Header (for loading segments)
 * ═══════════════════════════════════════════════════════════════════════════ */

typedef struct {
    uint32_t    p_type;                 /* Segment type */
    uint32_t    p_flags;                /* Segment flags */
    uint64_t    p_offset;               /* Segment file offset */
    uint64_t    p_vaddr;                /* Segment virtual address */
    uint64_t    p_paddr;                /* Segment physical address */
    uint64_t    p_filesz;               /* Segment size in file */
    uint64_t    p_memsz;                /* Segment size in memory */
    uint64_t    p_align;                /* Segment alignment */
} Elf64_Phdr;

/* p_type values */
#define PT_NULL         0               /* Unused entry */
#define PT_LOAD         1               /* Loadable segment */
#define PT_DYNAMIC      2               /* Dynamic linking info */
#define PT_INTERP       3               /* Interpreter pathname */
#define PT_NOTE         4               /* Auxiliary information */
#define PT_SHLIB        5               /* Reserved */
#define PT_PHDR         6               /* Program header table */
#define PT_TLS          7               /* Thread-local storage */
#define PT_GNU_EH_FRAME 0x6474e550      /* GCC .eh_frame_hdr segment */
#define PT_GNU_STACK    0x6474e551      /* Stack executability */
#define PT_GNU_RELRO    0x6474e552      /* Read-only after relocation */

/* p_flags values */
#define PF_X            0x1             /* Execute permission */
#define PF_W            0x2             /* Write permission */
#define PF_R            0x4             /* Read permission */

/* ═══════════════════════════════════════════════════════════════════════════
 * ELF64 Section Header (for debugging/symbols - not needed for loading)
 * ═══════════════════════════════════════════════════════════════════════════ */

typedef struct {
    uint32_t    sh_name;                /* Section name (string table index) */
    uint32_t    sh_type;                /* Section type */
    uint64_t    sh_flags;               /* Section flags */
    uint64_t    sh_addr;                /* Section virtual address */
    uint64_t    sh_offset;              /* Section file offset */
    uint64_t    sh_size;                /* Section size */
    uint32_t    sh_link;                /* Link to another section */
    uint32_t    sh_info;                /* Additional section info */
    uint64_t    sh_addralign;           /* Section alignment */
    uint64_t    sh_entsize;             /* Entry size if section holds table */
} Elf64_Shdr;

/* sh_type values */
#define SHT_NULL        0               /* Inactive section */
#define SHT_PROGBITS    1               /* Program-defined data */
#define SHT_SYMTAB      2               /* Symbol table */
#define SHT_STRTAB      3               /* String table */
#define SHT_RELA        4               /* Relocation with addends */
#define SHT_NOBITS      8               /* No file data (BSS) */

/* sh_flags values */
#define SHF_WRITE       0x1             /* Writable data */
#define SHF_ALLOC       0x2             /* Occupies memory */
#define SHF_EXECINSTR   0x4             /* Executable instructions */

/* ═══════════════════════════════════════════════════════════════════════════
 * ELF64 Symbol Table Entry (for debugging - optional)
 * ═══════════════════════════════════════════════════════════════════════════ */

typedef struct {
    uint32_t    st_name;                /* Symbol name (string table index) */
    uint8_t     st_info;                /* Symbol type and binding */
    uint8_t     st_other;               /* Symbol visibility */
    uint16_t    st_shndx;               /* Section index */
    uint64_t    st_value;               /* Symbol value */
    uint64_t    st_size;                /* Symbol size */
} Elf64_Sym;

/* Symbol binding (upper 4 bits of st_info) */
#define ELF64_ST_BIND(i)    ((i) >> 4)
#define STB_LOCAL       0               /* Local symbol */
#define STB_GLOBAL      1               /* Global symbol */
#define STB_WEAK        2               /* Weak symbol */

/* Symbol type (lower 4 bits of st_info) */
#define ELF64_ST_TYPE(i)    ((i) & 0xf)
#define STT_NOTYPE      0               /* No type */
#define STT_OBJECT      1               /* Data object */
#define STT_FUNC        2               /* Function */
#define STT_SECTION     3               /* Section */
#define STT_FILE        4               /* Source file */

/* ═══════════════════════════════════════════════════════════════════════════
 * ELF Validation Helpers
 *
 * Pure exokernel design: These are LIBOS helpers, not kernel code.
 * The kernel never sees ELF format - it just allocates pages.
 * ═══════════════════════════════════════════════════════════════════════════ */

/**
 * Check if buffer contains valid ELF64 header
 * @param ehdr Pointer to potential ELF header
 * @return 1 if valid ELF64, 0 otherwise
 */
static inline int elf64_is_valid(const Elf64_Ehdr *ehdr) {
    /* Check magic number */
    if (ehdr->e_ident[EI_MAG0] != 0x7f ||
        ehdr->e_ident[EI_MAG1] != 'E' ||
        ehdr->e_ident[EI_MAG2] != 'L' ||
        ehdr->e_ident[EI_MAG3] != 'F') {
        return 0;
    }

    /* Check 64-bit */
    if (ehdr->e_ident[EI_CLASS] != ELFCLASS64) {
        return 0;
    }

    /* Check executable */
    if (ehdr->e_type != ET_EXEC && ehdr->e_type != ET_DYN) {
        return 0;
    }

    return 1;
}

/**
 * Check if ELF is for current architecture
 * @param ehdr Valid ELF64 header
 * @return 1 if compatible, 0 otherwise
 */
static inline int elf64_arch_compatible(const Elf64_Ehdr *ehdr) {
#if defined(__x86_64__)
    return ehdr->e_machine == EM_X86_64;
#elif defined(__aarch64__)
    return ehdr->e_machine == EM_AARCH64;
#elif defined(__riscv) && (__riscv_xlen == 64)
    return ehdr->e_machine == EM_RISCV;
#else
    (void)ehdr;
    return 0;
#endif
}

/**
 * Get program header at index
 * @param ehdr ELF header
 * @param base Base address of ELF file in memory
 * @param idx Program header index
 * @return Pointer to program header, or NULL if out of bounds
 */
static inline const Elf64_Phdr *elf64_get_phdr(const Elf64_Ehdr *ehdr,
                                                const void *base,
                                                uint16_t idx) {
    if (idx >= ehdr->e_phnum) {
        return (const Elf64_Phdr *)0;
    }
    return (const Elf64_Phdr *)((const uint8_t *)base + ehdr->e_phoff +
                                 idx * ehdr->e_phentsize);
}

/**
 * Convert ELF flags to exokernel page permissions
 * @param p_flags ELF segment flags (PF_R, PF_W, PF_X)
 * @return Exokernel PERM_* flags
 *
 * Exokernel principle: The LibOS decides what permissions mean.
 * We translate ELF's view of permissions to our page table bits.
 */
static inline uint64_t elf64_flags_to_perm(uint32_t p_flags) {
    uint64_t perm = 0;

    /* PERM_R (0x1), PERM_W (0x2), PERM_X (0x4) - from exov6_interface.h */
    if (p_flags & PF_R) perm |= 0x1;  /* PERM_R */
    if (p_flags & PF_W) perm |= 0x2;  /* PERM_W */
    if (p_flags & PF_X) perm |= 0x4;  /* PERM_X */

    return perm;
}

/* ═══════════════════════════════════════════════════════════════════════════
 * Legacy ELF32 Compatibility (for reference - xv6 heritage)
 * ═══════════════════════════════════════════════════════════════════════════ */

#ifdef ELF32_SUPPORT

typedef struct {
    uint8_t     e_ident[EI_NIDENT];
    uint16_t    e_type;
    uint16_t    e_machine;
    uint32_t    e_version;
    uint32_t    e_entry;                /* 32-bit entry point */
    uint32_t    e_phoff;                /* 32-bit offset */
    uint32_t    e_shoff;
    uint32_t    e_flags;
    uint16_t    e_ehsize;
    uint16_t    e_phentsize;
    uint16_t    e_phnum;
    uint16_t    e_shentsize;
    uint16_t    e_shnum;
    uint16_t    e_shstrndx;
} Elf32_Ehdr;

typedef struct {
    uint32_t    p_type;
    uint32_t    p_offset;
    uint32_t    p_vaddr;
    uint32_t    p_paddr;
    uint32_t    p_filesz;
    uint32_t    p_memsz;
    uint32_t    p_flags;
    uint32_t    p_align;
} Elf32_Phdr;

#endif /* ELF32_SUPPORT */

#endif /* ELF_H */

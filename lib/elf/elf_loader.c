/**
 * @file elf_loader.c
 * @brief LibOS ELF Loader Implementation (Phase 10)
 *
 * PURE EXOKERNEL PHILOSOPHY IN ACTION:
 *
 *   This code runs in USER SPACE. The kernel has no idea what an "ELF" is.
 *   The kernel only provides raw primitives:
 *     - sys_page_alloc(): Get a physical page
 *     - sys_page_map(): Map it into virtual address space
 *
 *   We, the LibOS, do all the "smart" work:
 *     - Parse the ELF format
 *     - Decide where to put segments
 *     - Set up the stack
 *     - Handle BSS (zero-filled memory)
 *
 * This is exactly how MIT's ExOS worked on top of the Xok exokernel.
 *
 * Inspirations:
 *   - MIT Exokernel (1995): "The exokernel exports the hardware; applications
 *                            are free to do whatever they want with it."
 *   - seL4: User-space loaders with explicit memory capabilities
 *   - MirageOS/IncludeOS: At extreme, eliminates ELF entirely (compile-time linking)
 */

#include "elf_loader.h"
#include <elf.h>
#include <stdint.h>
#include <stddef.h>

/* ═══════════════════════════════════════════════════════════════════════════
 * LibOS Syscall Interface
 *
 * These are the raw kernel primitives we have to work with.
 * Everything else is OUR job (the LibOS).
 * ═══════════════════════════════════════════════════════════════════════════ */

/* From lib/syscall.c - raw syscall wrappers */
extern uint64_t sys_page_alloc_raw(void);
extern int sys_page_map_raw(int target_env, uint64_t phys, uint64_t virt, int perm);
extern int sys_env_create_raw(void);
extern int sys_env_run_raw(int env_id, uint64_t entry, uint64_t sp);

/* LibOS helpers */
extern void print(const char *s);
extern void print_hex(uint64_t n);

/* Permission bits (must match exov6_interface.h) */
#define PERM_R  0x1
#define PERM_W  0x2
#define PERM_X  0x4

/* ═══════════════════════════════════════════════════════════════════════════
 * Helper Functions
 * ═══════════════════════════════════════════════════════════════════════════ */

/* Simple memset for zero-filling BSS */
static void *elf_memset(void *dst, int c, size_t n) {
    uint8_t *d = (uint8_t *)dst;
    while (n-- > 0) {
        *d++ = (uint8_t)c;
    }
    return dst;
}

/* Simple memcpy for segment data */
static void *elf_memcpy(void *dst, const void *src, size_t n) {
    uint8_t *d = (uint8_t *)dst;
    const uint8_t *s = (const uint8_t *)src;
    while (n-- > 0) {
        *d++ = *s++;
    }
    return dst;
}

/* Round up to page boundary */
static uint64_t page_roundup(uint64_t addr) {
    return (addr + ELF_PAGE_SIZE - 1) & ~(ELF_PAGE_SIZE - 1);
}

/* Round down to page boundary */
static uint64_t page_rounddown(uint64_t addr) {
    return addr & ~(ELF_PAGE_SIZE - 1);
}

/* Convert ELF segment flags to exokernel permissions */
static int elf_flags_to_perm(uint32_t p_flags) {
    int perm = 0;
    if (p_flags & PF_R) perm |= PERM_R;
    if (p_flags & PF_W) perm |= PERM_W;
    if (p_flags & PF_X) perm |= PERM_X;
    return perm;
}

/* ═══════════════════════════════════════════════════════════════════════════
 * ELF Validation
 * ═══════════════════════════════════════════════════════════════════════════ */

int elf_validate(const void *elf_data, size_t elf_size) {
    if (elf_size < sizeof(Elf64_Ehdr)) {
        return ELF_ERR_BADMAGIC;
    }

    const Elf64_Ehdr *ehdr = (const Elf64_Ehdr *)elf_data;

    /* Check ELF magic */
    if (ehdr->e_ident[EI_MAG0] != 0x7f ||
        ehdr->e_ident[EI_MAG1] != 'E' ||
        ehdr->e_ident[EI_MAG2] != 'L' ||
        ehdr->e_ident[EI_MAG3] != 'F') {
        return ELF_ERR_BADMAGIC;
    }

    /* Check 64-bit */
    if (ehdr->e_ident[EI_CLASS] != ELFCLASS64) {
        return ELF_ERR_BADCLASS;
    }

    /* Check architecture */
#if defined(__x86_64__)
    if (ehdr->e_machine != EM_X86_64) {
        return ELF_ERR_BADARCH;
    }
#elif defined(__aarch64__)
    if (ehdr->e_machine != EM_AARCH64) {
        return ELF_ERR_BADARCH;
    }
#else
    return ELF_ERR_BADARCH;
#endif

    /* Check executable type */
    if (ehdr->e_type != ET_EXEC && ehdr->e_type != ET_DYN) {
        return ELF_ERR_BADMAGIC;
    }

    /* Validate program header offset */
    if (ehdr->e_phoff + ehdr->e_phnum * ehdr->e_phentsize > elf_size) {
        return ELF_ERR_BADPHDR;
    }

    return ELF_OK;
}

const char *elf_strerror(int error) {
    switch (error) {
        case ELF_OK:           return "Success";
        case ELF_ERR_NOFILE:   return "File not found";
        case ELF_ERR_BADMAGIC: return "Invalid ELF magic number";
        case ELF_ERR_BADCLASS: return "Not a 64-bit ELF";
        case ELF_ERR_BADARCH:  return "Wrong architecture";
        case ELF_ERR_NOMEM:    return "Out of memory";
        case ELF_ERR_MAPERR:   return "Page mapping failed";
        case ELF_ERR_TOOBIG:   return "ELF file too large";
        case ELF_ERR_BADPHDR:  return "Invalid program header";
        default:               return "Unknown error";
    }
}

/* ═══════════════════════════════════════════════════════════════════════════
 * Load ELF into Current Address Space
 *
 * This is for self-exec: replace current process with new program.
 * In a full implementation, we'd unmap old memory first.
 * ═══════════════════════════════════════════════════════════════════════════ */

int elf_load_from_memory(const void *elf_data, size_t elf_size,
                         struct elf_load_result *result) {
    int err;

    /* Initialize result */
    result->entry_point = 0;
    result->stack_top = 0;
    result->brk = 0;
    result->error = 0;

    /* Validate ELF */
    err = elf_validate(elf_data, elf_size);
    if (err != ELF_OK) {
        result->error = err;
        return err;
    }

    const Elf64_Ehdr *ehdr = (const Elf64_Ehdr *)elf_data;
    const uint8_t *elf_bytes = (const uint8_t *)elf_data;

    print("[ELF] Loading ELF64 executable\n");
    print("      Entry point: 0x");
    print_hex(ehdr->e_entry);
    print("\n");
    print("      Program headers: ");
    print_hex(ehdr->e_phnum);
    print("\n");

    /* Track highest loaded address for brk */
    uint64_t max_addr = 0;

    /* Process each program header */
    for (uint16_t i = 0; i < ehdr->e_phnum; i++) {
        const Elf64_Phdr *phdr = (const Elf64_Phdr *)
            (elf_bytes + ehdr->e_phoff + i * ehdr->e_phentsize);

        /* Only process loadable segments */
        if (phdr->p_type != PT_LOAD) {
            continue;
        }

        print("[ELF] Segment ");
        print_hex(i);
        print(": vaddr=0x");
        print_hex(phdr->p_vaddr);
        print(" memsz=0x");
        print_hex(phdr->p_memsz);
        print(" filesz=0x");
        print_hex(phdr->p_filesz);
        print("\n");

        /* Calculate page-aligned region */
        uint64_t va_start = page_rounddown(phdr->p_vaddr);
        uint64_t va_end = page_roundup(phdr->p_vaddr + phdr->p_memsz);
        int perm = elf_flags_to_perm(phdr->p_flags);

        /* Allocate and map pages for this segment */
        for (uint64_t va = va_start; va < va_end; va += ELF_PAGE_SIZE) {
            /* Allocate physical page */
            uint64_t pa = sys_page_alloc_raw();
            if ((int64_t)pa < 0) {
                print("[ELF] ERROR: sys_page_alloc failed\n");
                result->error = ELF_ERR_NOMEM;
                return ELF_ERR_NOMEM;
            }

            /* Map page (target_env=0 means self) */
            err = sys_page_map_raw(0, pa, va, perm);
            if (err < 0) {
                print("[ELF] ERROR: sys_page_map failed at 0x");
                print_hex(va);
                print("\n");
                result->error = ELF_ERR_MAPERR;
                return ELF_ERR_MAPERR;
            }
        }

        /* Copy segment data from file */
        if (phdr->p_filesz > 0) {
            /* Check bounds */
            if (phdr->p_offset + phdr->p_filesz > elf_size) {
                result->error = ELF_ERR_BADPHDR;
                return ELF_ERR_BADPHDR;
            }

            /* Copy file content */
            elf_memcpy((void *)phdr->p_vaddr,
                       elf_bytes + phdr->p_offset,
                       phdr->p_filesz);
        }

        /* Zero BSS (memory beyond file data) */
        if (phdr->p_memsz > phdr->p_filesz) {
            elf_memset((void *)(phdr->p_vaddr + phdr->p_filesz),
                       0,
                       phdr->p_memsz - phdr->p_filesz);
        }

        /* Track maximum address */
        if (phdr->p_vaddr + phdr->p_memsz > max_addr) {
            max_addr = phdr->p_vaddr + phdr->p_memsz;
        }
    }

    /* Allocate stack */
    print("[ELF] Allocating stack at 0x");
    print_hex(ELF_STACK_TOP - ELF_DEFAULT_STACK_SIZE);
    print("\n");

    uint64_t stack_bottom = ELF_STACK_TOP - ELF_DEFAULT_STACK_SIZE;
    for (uint64_t va = stack_bottom; va < ELF_STACK_TOP; va += ELF_PAGE_SIZE) {
        uint64_t pa = sys_page_alloc_raw();
        if ((int64_t)pa < 0) {
            result->error = ELF_ERR_NOMEM;
            return ELF_ERR_NOMEM;
        }

        err = sys_page_map_raw(0, pa, va, PERM_R | PERM_W);
        if (err < 0) {
            result->error = ELF_ERR_MAPERR;
            return ELF_ERR_MAPERR;
        }
    }

    /* Zero stack */
    elf_memset((void *)stack_bottom, 0, ELF_DEFAULT_STACK_SIZE);

    /* Fill in result */
    result->entry_point = ehdr->e_entry;
    result->stack_top = ELF_STACK_TOP;
    result->brk = page_roundup(max_addr);
    result->error = ELF_OK;

    print("[ELF] Load complete\n");
    print("      Entry: 0x");
    print_hex(result->entry_point);
    print("\n");
    print("      Stack: 0x");
    print_hex(result->stack_top);
    print("\n");
    print("      Brk:   0x");
    print_hex(result->brk);
    print("\n");

    return ELF_OK;
}

/* ═══════════════════════════════════════════════════════════════════════════
 * Load ELF into Child Environment
 *
 * This is for spawn: create a new process from an ELF file.
 * Following pure exokernel design:
 *   1. Create blank environment (kernel does this)
 *   2. Allocate and map memory (LibOS does this)
 *   3. Start execution (kernel does this on our request)
 * ═══════════════════════════════════════════════════════════════════════════ */

int elf_load_into_child(const void *elf_data, size_t elf_size,
                        struct elf_load_result *result) {
    int err;

    /* Initialize result */
    result->entry_point = 0;
    result->stack_top = 0;
    result->brk = 0;
    result->error = 0;

    /* Validate ELF first */
    err = elf_validate(elf_data, elf_size);
    if (err != ELF_OK) {
        result->error = err;
        return err;
    }

    /* Create blank child environment */
    int child_pid = sys_env_create_raw();
    if (child_pid < 0) {
        print("[ELF] ERROR: sys_env_create failed\n");
        result->error = ELF_ERR_NOMEM;
        return child_pid;
    }

    print("[ELF] Created child environment PID ");
    print_hex(child_pid);
    print("\n");

    const Elf64_Ehdr *ehdr = (const Elf64_Ehdr *)elf_data;
    const uint8_t *elf_bytes = (const uint8_t *)elf_data;

    uint64_t max_addr = 0;

    /* Process each program header */
    for (uint16_t i = 0; i < ehdr->e_phnum; i++) {
        const Elf64_Phdr *phdr = (const Elf64_Phdr *)
            (elf_bytes + ehdr->e_phoff + i * ehdr->e_phentsize);

        if (phdr->p_type != PT_LOAD) {
            continue;
        }

        uint64_t va_start = page_rounddown(phdr->p_vaddr);
        uint64_t va_end = page_roundup(phdr->p_vaddr + phdr->p_memsz);
        int perm = elf_flags_to_perm(phdr->p_flags);

        /* For child loading, we need to:
         * 1. Allocate page
         * 2. Map into OUR address space temporarily to copy data
         * 3. Remap into CHILD's address space
         *
         * This is the challenge of loading another process's memory.
         * In a real system we'd use shared memory or a kernel copy.
         *
         * SIMPLIFICATION: For now, we just map directly into child
         * and rely on the kernel to initialize pages to zero.
         * A full implementation would use shared page mapping.
         */
        for (uint64_t va = va_start; va < va_end; va += ELF_PAGE_SIZE) {
            uint64_t pa = sys_page_alloc_raw();
            if ((int64_t)pa < 0) {
                print("[ELF] ERROR: page alloc failed for child\n");
                result->error = ELF_ERR_NOMEM;
                return ELF_ERR_NOMEM;
            }

            /* Map into child's address space */
            err = sys_page_map_raw(child_pid, pa, va, perm);
            if (err < 0) {
                print("[ELF] ERROR: page map failed for child at 0x");
                print_hex(va);
                print("\n");
                result->error = ELF_ERR_MAPERR;
                return ELF_ERR_MAPERR;
            }

            /* Also map temporarily into our space to copy data */
            /* Use a high temporary address */
            uint64_t temp_va = 0x7000000000ULL + (va - va_start);
            err = sys_page_map_raw(0, pa, temp_va, PERM_R | PERM_W);
            if (err < 0) {
                /* If we can't map temporarily, skip data copy */
                continue;
            }

            /* Zero the page first */
            elf_memset((void *)temp_va, 0, ELF_PAGE_SIZE);

            /* Copy segment data if this page overlaps with file content */
            if (va < phdr->p_vaddr + phdr->p_filesz) {
                uint64_t file_start = (va <= phdr->p_vaddr) ?
                                      phdr->p_vaddr : va;
                uint64_t file_end = (va + ELF_PAGE_SIZE > phdr->p_vaddr + phdr->p_filesz) ?
                                    phdr->p_vaddr + phdr->p_filesz : va + ELF_PAGE_SIZE;

                if (file_end > file_start) {
                    uint64_t offset_in_page = file_start - va;
                    uint64_t offset_in_file = file_start - phdr->p_vaddr + phdr->p_offset;
                    uint64_t copy_len = file_end - file_start;

                    if (offset_in_file + copy_len <= elf_size) {
                        elf_memcpy((void *)(temp_va + offset_in_page),
                                   elf_bytes + offset_in_file,
                                   copy_len);
                    }
                }
            }

            /* TODO: Unmap temporary page (sys_page_unmap) */
        }

        if (phdr->p_vaddr + phdr->p_memsz > max_addr) {
            max_addr = phdr->p_vaddr + phdr->p_memsz;
        }
    }

    /* Allocate stack for child */
    uint64_t stack_bottom = ELF_STACK_TOP - ELF_DEFAULT_STACK_SIZE;
    for (uint64_t va = stack_bottom; va < ELF_STACK_TOP; va += ELF_PAGE_SIZE) {
        uint64_t pa = sys_page_alloc_raw();
        if ((int64_t)pa < 0) {
            result->error = ELF_ERR_NOMEM;
            return ELF_ERR_NOMEM;
        }

        err = sys_page_map_raw(child_pid, pa, va, PERM_R | PERM_W);
        if (err < 0) {
            result->error = ELF_ERR_MAPERR;
            return ELF_ERR_MAPERR;
        }
    }

    /* Fill in result */
    result->entry_point = ehdr->e_entry;
    result->stack_top = ELF_STACK_TOP;
    result->brk = page_roundup(max_addr);
    result->error = ELF_OK;

    print("[ELF] Child PID ");
    print_hex(child_pid);
    print(" loaded, entry=0x");
    print_hex(result->entry_point);
    print("\n");

    /* Return child PID (caller will call sys_env_run to start it) */
    return child_pid;
}

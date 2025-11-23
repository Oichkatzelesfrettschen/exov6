/**
 * @file elf_loader.h
 * @brief LibOS ELF Loader Interface (Phase 10)
 *
 * PURE EXOKERNEL/LIBOS DESIGN:
 *
 *   The KERNEL provides only:
 *     - sys_env_create()  -> Create blank environment
 *     - sys_page_alloc()  -> Allocate physical page
 *     - sys_page_map()    -> Map page into address space
 *     - sys_env_run()     -> Start/resume environment
 *
 *   The LIBOS does everything else:
 *     - Reading ELF from disk (via fs_srv IPC)
 *     - Parsing ELF headers
 *     - Allocating and mapping memory for segments
 *     - Setting up stack and entry point
 *
 * This is inspired by:
 *   - MIT Exokernel: User-space ELF loader in ExOS
 *   - seL4: User-space process loader
 *   - Unikernel: Compile-time linking (MirageOS eliminates ELF parsing)
 */

#ifndef ELF_LOADER_H
#define ELF_LOADER_H

#include <stdint.h>
#include <stddef.h>  /* For size_t in freestanding mode */
#include <elf.h>

/* Ensure size_t is available */
#ifndef __SIZE_TYPE__
typedef uint64_t size_t;
#endif

/* ═══════════════════════════════════════════════════════════════════════════
 * ELF Loading Result
 * ═══════════════════════════════════════════════════════════════════════════ */

struct elf_load_result {
    uint64_t entry_point;       /* Entry point address (e_entry) */
    uint64_t stack_top;         /* Top of allocated stack */
    uint64_t brk;               /* Initial break (end of loaded segments) */
    int error;                  /* 0 on success, negative on error */
};

/* Error codes */
#define ELF_OK              0
#define ELF_ERR_NOFILE      -1  /* File not found */
#define ELF_ERR_BADMAGIC    -2  /* Invalid ELF magic */
#define ELF_ERR_BADCLASS    -3  /* Not ELF64 */
#define ELF_ERR_BADARCH     -4  /* Wrong architecture */
#define ELF_ERR_NOMEM       -5  /* Out of memory */
#define ELF_ERR_MAPERR      -6  /* Page mapping failed */
#define ELF_ERR_TOOBIG      -7  /* ELF file too large */
#define ELF_ERR_BADPHDR     -8  /* Invalid program header */

/* ═══════════════════════════════════════════════════════════════════════════
 * ELF Loading Configuration
 * ═══════════════════════════════════════════════════════════════════════════ */

/* Default user stack size (64KB) */
#define ELF_DEFAULT_STACK_SIZE  (16 * 4096)

/* Stack grows down from this address */
#define ELF_STACK_TOP           0x7FFFFFFFF000ULL

/* Maximum ELF file size to load (16MB) */
#define ELF_MAX_FILE_SIZE       (16 * 1024 * 1024)

/* Page size (must match kernel) */
#define ELF_PAGE_SIZE           4096

/* ═══════════════════════════════════════════════════════════════════════════
 * API Functions
 * ═══════════════════════════════════════════════════════════════════════════ */

/**
 * Load ELF from memory buffer into current address space (self-exec)
 *
 * This function:
 *   1. Validates ELF headers
 *   2. Allocates pages for each PT_LOAD segment
 *   3. Maps pages with correct permissions (R/W/X)
 *   4. Copies segment data from buffer
 *   5. Allocates and maps stack pages
 *
 * @param elf_data    Pointer to ELF file data in memory
 * @param elf_size    Size of ELF file data
 * @param result      Output: loading result with entry point, stack
 * @return            0 on success, negative error code on failure
 */
int elf_load_from_memory(const void *elf_data, size_t elf_size,
                         struct elf_load_result *result);

/**
 * Load ELF into a child environment
 *
 * This function:
 *   1. Creates new environment (sys_env_create)
 *   2. Loads ELF segments into child's address space
 *   3. Sets up child's stack
 *   4. Does NOT start the child (call sys_env_run separately)
 *
 * @param elf_data    Pointer to ELF file data in memory
 * @param elf_size    Size of ELF file data
 * @param result      Output: loading result with entry point, stack
 * @return            Child PID on success, negative error code on failure
 */
int elf_load_into_child(const void *elf_data, size_t elf_size,
                        struct elf_load_result *result);

/**
 * Validate ELF header without loading
 *
 * @param elf_data    Pointer to ELF file data
 * @param elf_size    Size of data (must be at least sizeof(Elf64_Ehdr))
 * @return            0 if valid ELF64 for this architecture, error code otherwise
 */
int elf_validate(const void *elf_data, size_t elf_size);

/**
 * Get human-readable error message
 *
 * @param error       Error code from elf_load_*
 * @return            Static error message string
 */
const char *elf_strerror(int error);

#endif /* ELF_LOADER_H */

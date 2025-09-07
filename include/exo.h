#pragma once

/**
 * @file exo.h
 * @brief Exokernel interface for libos and userland
 * 
 * Pure C17 implementation providing exokernel abstractions.
 */

#include <stdint.h>
#include <stddef.h>
#include <time.h>
#include "types.h"

// Hash for capability authentication
typedef struct hash256 {
    uint64_t parts[4];
} hash256_t;

// Exokernel capability structure
typedef struct exo_cap {
    uint32_t pa;         // Physical address (if memory cap)
    uint32_t id;         // Resource identifier
    uint32_t rights;     // Rights bitmask
    uint32_t owner;      // Owner process/zone
    hash256_t auth_tag;  // Authentication tag
} exo_cap;

// Block device capability
typedef struct exo_blockcap {
    uint32_t dev;        // Device number
    uint32_t blockno;    // Block number
    uint32_t rights;     // Rights bitmask
    uint32_t owner;      // Owner process/zone
} exo_blockcap;

// Rights flags
#define EXO_RIGHT_READ    0x01
#define EXO_RIGHT_WRITE   0x02
#define EXO_RIGHT_EXEC    0x04
#define EXO_RIGHT_SHARE   0x08
#define EXO_RIGHT_GRANT   0x10

// Memory protection flags (for mmap compatibility)
#define EXO_PROT_READ     0x01
#define EXO_PROT_WRITE    0x02
#define EXO_PROT_EXEC     0x04

// Exokernel syscall interface
int exo_syscall(int num, ...);

// Memory capabilities
exo_cap exo_alloc_page(void);
int exo_unbind_page(exo_cap c);
int exo_map_page(exo_cap c, void* va);

// IPC operations
int exo_send(exo_cap dest, const void* msg, size_t size);
int exo_recv(exo_cap src, void* msg, size_t size);

// Capability operations
exo_cap cap_new(uint32_t id, uint32_t rights, uint32_t owner);
int cap_verify(exo_cap c);
int exo_cap_revoke(exo_cap c);  // Renamed to avoid conflict with cap.h

// Memory capability management
int exo_unmap_capability(exo_cap cap, void* addr);
int exo_release_capability(exo_cap cap);
int exo_set_protection(exo_cap cap, int prot);
int exo_sync_memory(exo_cap cap, int async);
int exo_lock_memory(exo_cap cap, void* addr, size_t len);
int exo_unlock_memory(exo_cap cap, void* addr, size_t len);
exo_cap exo_request_memory(size_t len, int prot);
void* exo_map_capability(exo_cap cap, void* addr, size_t len, int prot);
exo_cap fd_to_capability(int fd);
int exo_bind_memory_file(exo_cap mem_cap, exo_cap file_cap, size_t offset);

// Process management
int exo_yield(void);
int exo_yield_to(exo_cap target);
int exo_exit(int status);
exo_cap exo_create_process_cap(void);
exo_cap exo_request_cpu(void);
int exo_schedule_process(exo_cap proc_cap, exo_cap cpu_cap);
exo_cap exo_create_cow_mapping(exo_cap parent_mem, size_t size);
int exo_mark_cow(exo_cap mem_cap, void* addr, size_t len);
int exo_set_scheduling_hint(exo_cap cpu_cap, int priority);

// Process execution support
int begin_exec(void);
void abort_exec(void);
void free_process(void* proc);

// Timer and clock functions
exo_cap exo_request_timer(void);
time_t exo_get_boot_time(exo_cap timer_cap);
uint64_t exo_get_ticks(exo_cap timer_cap);
uint64_t exo_get_tick_rate(exo_cap timer_cap);
uint64_t exo_get_monotonic_ns(exo_cap timer_cap);
uint64_t exo_get_process_time_ns(exo_cap timer_cap);
uint64_t exo_get_thread_time_ns(exo_cap timer_cap);
int exo_set_system_time(exo_cap timer_cap, uint64_t ns_since_epoch);
int exo_sleep_ns(exo_cap timer_cap, uint64_t sleep_ns);
exo_cap exo_set_timer(exo_cap timer_cap, uint64_t timeout_ns, int signal);
uint64_t exo_cancel_timer(exo_cap timer_cap);
int exo_get_process_times(exo_cap timer_cap, uint64_t *user_time, uint64_t *sys_time,
                         uint64_t *child_user_time, uint64_t *child_sys_time);
uint64_t exo_get_clk_tck(exo_cap timer_cap);

// Console output (for debugging)
void cprintf(const char* fmt, ...);

// Static assertions for structure sizes
_Static_assert(sizeof(exo_cap) <= 64, "Capability too large");
_Static_assert(sizeof(hash256_t) == 32, "Hash must be 256 bits");
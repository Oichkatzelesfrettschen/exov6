/*
 * zone_isolation.c - Implementation of exokernel zone isolation mechanisms
 */

#include "zone_isolation.h"
#include "defs.h"
#include "spinlock.h"
#include "kalloc.h"
#include "mmu.h"  /* Changed from vm.h to mmu.h */
#include <string.h>
#include <stdatomic.h>
#include "proc.h"
#include "timing.h"

/* Maximum number of zones */
#define MAX_ZONES 32

/* Zone table */
static zone_desc_t zone_table[MAX_ZONES];
static struct spinlock zone_lock;
static bool zone_initialized = false;

/* Zone statistics */
static zone_stats_t zone_stats[MAX_ZONES];

/* Zone verification magic number */
#define ZONE_MAGIC 0x20E5AFE

/*
 * Initialize zone isolation subsystem
 */
void zone_isolation_init(void) {
    initlock(&zone_lock, "zone_isolation");
    memset(zone_table, 0, sizeof(zone_table));
    memset(zone_stats, 0, sizeof(zone_stats));
    
    /* Register kernel zone */
    zone_register(ZONE_KERNEL, (void *)KERNBASE, KERNSIZE, ZONE_PROT_FULL);
    zone_table[0].flags.isolated = 1;
    zone_table[0].flags.active = 1;
    zone_table[0].flags.locked = 1;  /* Kernel zone is always locked */
    
    zone_initialized = true;
}

/*
 * Register a new zone
 */
int zone_register(zone_id_t id, void *base, size_t size, uint32_t prot) {
    if (!zone_initialized && id != ZONE_KERNEL) {
        return -1;  /* Only kernel zone can be registered before init */
    }
    
    acquire(&zone_lock);
    
    /* Find free slot */
    int slot = -1;
    for (int i = 0; i < MAX_ZONES; i++) {
        if (zone_table[i].id == id) {
            release(&zone_lock);
            return -2;  /* Zone already registered */
        }
        if (zone_table[i].id == 0 && slot == -1) {
            slot = i;
        }
    }
    
    if (slot == -1) {
        release(&zone_lock);
        return -3;  /* No free slots */
    }
    
    /* Initialize zone descriptor */
    zone_table[slot].id = id;
    zone_table[slot].protection = prot;
    zone_table[slot].base_addr = base;
    zone_table[slot].size = size;
    zone_table[slot].zone_cap = 0;  /* Will be allocated later */
    zone_table[slot].owner_pid = 0;
    zone_table[slot].flags.isolated = 0;
    zone_table[slot].flags.active = 1;
    zone_table[slot].flags.locked = 0;
    zone_table[slot].flags.quantum = 0;
    
    release(&zone_lock);
    return 0;
}

/*
 * Unregister a zone
 */
int zone_unregister(zone_id_t id) {
    if (id == ZONE_KERNEL) {
        return -1;  /* Cannot unregister kernel zone */
    }
    
    acquire(&zone_lock);
    
    for (int i = 0; i < MAX_ZONES; i++) {
        if (zone_table[i].id == id) {
            if (zone_table[i].flags.locked) {
                release(&zone_lock);
                return -2;  /* Zone is locked */
            }
            
            /* Clear zone entry */
            memset(&zone_table[i], 0, sizeof(zone_desc_t));
            memset(&zone_stats[i], 0, sizeof(zone_stats_t));
            
            release(&zone_lock);
            return 0;
        }
    }
    
    release(&zone_lock);
    return -3;  /* Zone not found */
}

/*
 * Check if an address belongs to a zone
 */
zone_id_t zone_get_id(void *addr) {
    uintptr_t addr_val = (uintptr_t)addr;
    
    acquire(&zone_lock);
    
    for (int i = 0; i < MAX_ZONES; i++) {
        if (zone_table[i].id != 0 && zone_table[i].flags.active) {
            uintptr_t base = (uintptr_t)zone_table[i].base_addr;
            uintptr_t end = base + zone_table[i].size;
            
            if (addr_val >= base && addr_val < end) {
                zone_id_t id = zone_table[i].id;
                release(&zone_lock);
                return id;
            }
        }
    }
    
    release(&zone_lock);
    return ZONE_INVALID;
}

/*
 * Validate cross-zone access
 */
zone_check_result_t zone_check_access(zone_id_t from, zone_id_t to,
                                      uint32_t requested_prot, cap_id_t cap) {
    if (from == ZONE_INVALID || to == ZONE_INVALID) {
        return ZONE_CHECK_INVALID_ZONE;
    }
    
    /* Kernel zone can access anything */
    if (from == ZONE_KERNEL) {
        return ZONE_CHECK_OK;
    }
    
    /* Same zone access is always allowed */
    if (from == to) {
        return ZONE_CHECK_OK;
    }
    
    acquire(&zone_lock);
    
    /* Find source and destination zones */
    zone_desc_t *from_zone = NULL;
    zone_desc_t *to_zone = NULL;
    
    for (int i = 0; i < MAX_ZONES; i++) {
        if (zone_table[i].id == from) {
            from_zone = &zone_table[i];
            zone_stats[i].transitions_out++;
        }
        if (zone_table[i].id == to) {
            to_zone = &zone_table[i];
            zone_stats[i].transitions_in++;
        }
    }
    
    if (!from_zone || !to_zone) {
        release(&zone_lock);
        return ZONE_CHECK_INVALID_ZONE;
    }
    
    /* Check if transition requires capability */
    if (to_zone->protection & ZONE_PROT_CAP) {
        if (cap == 0) {
            for (int i = 0; i < MAX_ZONES; i++) {
                if (zone_table[i].id == to) {
                    zone_stats[i].cap_failures++;
                    break;
                }
            }
            release(&zone_lock);
            return ZONE_CHECK_CAP_REQUIRED;
        }
        
        /* Validate capability using external validation */
        struct cap_entry cap_entry;
        cap_validation_result_t result = cap_validate_unified(cap, &cap_entry);
        
        if (result != VALIDATION_SUCCESS) {
            for (int i = 0; i < MAX_ZONES; i++) {
                if (zone_table[i].id == to) {
                    zone_stats[i].cap_failures++;
                    break;
                }
            }
            release(&zone_lock);
            return ZONE_CHECK_DENIED;
        }
        
        for (int i = 0; i < MAX_ZONES; i++) {
            if (zone_table[i].id == to) {
                zone_stats[i].cap_checks++;
                break;
            }
        }
    }
    
    /* Check protection flags */
    if ((to_zone->protection & requested_prot) != requested_prot) {
        for (int i = 0; i < MAX_ZONES; i++) {
            if (zone_table[i].id == to) {
                zone_stats[i].access_violations++;
                break;
            }
        }
        release(&zone_lock);
        return ZONE_CHECK_DENIED;
    }
    
    release(&zone_lock);
    return ZONE_CHECK_OK;
}

/*
 * Perform zone transition with capability check
 */
int zone_transition(zone_id_t target, cap_id_t cap, zone_transition_t *ctx) {
    if (!ctx) {
        return -1;
    }
    
    /* Get current zone from caller address */
    void *caller = __builtin_return_address(0);
    zone_id_t current = zone_get_id(caller);
    
    /* Fill transition context */
    ctx->from_zone = current;
    ctx->to_zone = target;
    ctx->transition_cap = cap;
    ctx->timestamp = audit_timestamp();  /* Serialized timestamp for audit */
    
    /* Save register state (simplified) */
    /* In a real implementation, this would save all registers */
    memset(ctx->saved_state, 0, sizeof(ctx->saved_state));
    
    /* Check if transition is allowed */
    zone_check_result_t check = zone_check_access(current, target, 
                                                  ZONE_PROT_CALL, cap);
    if (check != ZONE_CHECK_OK) {
        return -2;
    }
    
    /* Perform the transition */
    /* In a real implementation, this would:
     * 1. Switch page tables if necessary
     * 2. Update segment registers
     * 3. Clear sensitive registers
     * 4. Jump to target zone entry point
     */
    
    return 0;
}

/*
 * Lock a zone (prevent modifications)
 */
int zone_lock(zone_id_t id) {
    if (id == ZONE_KERNEL) {
        return 0;  /* Kernel zone is always locked */
    }
    
    acquire(&zone_lock);
    
    for (int i = 0; i < MAX_ZONES; i++) {
        if (zone_table[i].id == id) {
            zone_table[i].flags.locked = 1;
            release(&zone_lock);
            return 0;
        }
    }
    
    release(&zone_lock);
    return -1;  /* Zone not found */
}

/*
 * Unlock a zone
 */
int zone_unlock(zone_id_t id) {
    if (id == ZONE_KERNEL) {
        return -1;  /* Cannot unlock kernel zone */
    }
    
    acquire(&zone_lock);
    
    for (int i = 0; i < MAX_ZONES; i++) {
        if (zone_table[i].id == id) {
            zone_table[i].flags.locked = 0;
            release(&zone_lock);
            return 0;
        }
    }
    
    release(&zone_lock);
    return -1;  /* Zone not found */
}

/*
 * Get zone descriptor
 */
zone_desc_t *zone_get_desc(zone_id_t id) {
    acquire(&zone_lock);
    
    for (int i = 0; i < MAX_ZONES; i++) {
        if (zone_table[i].id == id) {
            zone_desc_t *desc = &zone_table[i];
            release(&zone_lock);
            return desc;
        }
    }
    
    release(&zone_lock);
    return NULL;
}

/*
 * Verify zone isolation integrity
 */
bool zone_verify_isolation(void) {
    acquire(&zone_lock);
    
    /* Check for overlapping zones */
    for (int i = 0; i < MAX_ZONES; i++) {
        if (zone_table[i].id == 0) continue;
        
        uintptr_t base1 = (uintptr_t)zone_table[i].base_addr;
        uintptr_t end1 = base1 + zone_table[i].size;
        
        for (int j = i + 1; j < MAX_ZONES; j++) {
            if (zone_table[j].id == 0) continue;
            
            uintptr_t base2 = (uintptr_t)zone_table[j].base_addr;
            uintptr_t end2 = base2 + zone_table[j].size;
            
            /* Check for overlap */
            if ((base1 < end2) && (base2 < end1)) {
                release(&zone_lock);
                return false;  /* Zones overlap */
            }
        }
    }
    
    /* Verify kernel zone is properly configured */
    bool kernel_found = false;
    for (int i = 0; i < MAX_ZONES; i++) {
        if (zone_table[i].id == ZONE_KERNEL) {
            if (!zone_table[i].flags.locked || !zone_table[i].flags.active) {
                release(&zone_lock);
                return false;  /* Kernel zone misconfigured */
            }
            kernel_found = true;
            break;
        }
    }
    
    if (!kernel_found) {
        release(&zone_lock);
        return false;  /* Kernel zone not found */
    }
    
    release(&zone_lock);
    return true;
}

/*
 * Zone-specific memory allocation
 */
void *zone_malloc(zone_id_t zone, size_t size) {
    zone_desc_t *desc = zone_get_desc(zone);
    if (!desc) {
        return NULL;
    }
    
    /* Allocate memory from zone's heap */
    /* This is a simplified implementation */
    void *ptr = kalloc();  /* Use kernel allocator for now */
    
    if (ptr) {
        /* Tag memory with zone ID */
        /* In a real implementation, this would update page tables */
    }
    
    return ptr;
}

/*
 * Free zone-allocated memory
 */
void zone_free(zone_id_t zone, void *ptr) {
    if (!ptr) return;
    
    /* Verify pointer belongs to zone */
    if (zone_get_id(ptr) != zone) {
        panic("zone_free: pointer not in zone");
    }
    
    kfree(ptr);
}

/*
 * Map memory between zones (requires capability)
 */
void *zone_map(zone_id_t from, zone_id_t to, void *addr, size_t size, cap_id_t cap) {
    /* Check capability authorizes mapping */
    zone_check_result_t check = zone_check_access(from, to, 
                                                  ZONE_PROT_READ | ZONE_PROT_WRITE, 
                                                  cap);
    if (check != ZONE_CHECK_OK) {
        return NULL;
    }
    
    /* Create mapping in page tables */
    /* This is a simplified implementation */
    return addr;  /* Return mapped address */
}

/*
 * Unmap cross-zone mapping
 */
int zone_unmap(void *addr, size_t size) {
    /* Remove mapping from page tables */
    /* This is a simplified implementation */
    return 0;
}

/*
 * Get zone statistics
 */
zone_stats_t *zone_get_stats(zone_id_t id) {
    acquire(&zone_lock);
    
    for (int i = 0; i < MAX_ZONES; i++) {
        if (zone_table[i].id == id) {
            zone_stats_t *stats = &zone_stats[i];
            release(&zone_lock);
            return stats;
        }
    }
    
    release(&zone_lock);
    return NULL;
}

/*
 * Dump zone information (debug)
 */
void zone_dump_info(zone_id_t id) {
    zone_desc_t *desc = zone_get_desc(id);
    zone_stats_t *stats = zone_get_stats(id);
    
    if (!desc) {
        cprintf("Zone 0x%x: Not found\n", id);
        return;
    }
    
    cprintf("Zone 0x%x:\n", id);
    cprintf("  Base: %p, Size: 0x%lx\n", desc->base_addr, desc->size);
    cprintf("  Protection: 0x%x\n", desc->protection);
    cprintf("  Flags: isolated=%d active=%d locked=%d quantum=%d\n",
            desc->flags.isolated, desc->flags.active, 
            desc->flags.locked, desc->flags.quantum);
    
    if (stats) {
        cprintf("  Stats:\n");
        cprintf("    Transitions in:  %llu\n", stats->transitions_in);
        cprintf("    Transitions out: %llu\n", stats->transitions_out);
        cprintf("    Violations:      %llu\n", stats->access_violations);
        cprintf("    Cap checks:      %llu\n", stats->cap_checks);
        cprintf("    Cap failures:    %llu\n", stats->cap_failures);
    }
}
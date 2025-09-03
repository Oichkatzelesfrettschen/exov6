#pragma once

/*
 * zone_isolation.h - Exokernel Zone Isolation and Protection Mechanisms
 * 
 * Enforces strict separation between:
 *  - Kernel Zone (Ring 0, privileged)
 *  - LibOS Zone (Ring 3, user-space OS services)
 *  - Application Zone (Ring 3, user applications)
 * 
 * Uses capability-based security for cross-zone communication
 */

#include <stdint.h>
#include <stdbool.h>
#include "cap.h"

#ifdef __cplusplus
extern "C" {
#endif

/* Zone identifiers */
typedef enum {
    ZONE_KERNEL     = 0x0000,  /* Kernel privileged zone */
    ZONE_LIBOS      = 0x1000,  /* LibOS service zone */
    ZONE_APP        = 0x2000,  /* Application zone */
    ZONE_DRIVER     = 0x3000,  /* Device driver zone */
    ZONE_HYPERVISOR = 0x4000,  /* Hypervisor zone (if virtualized) */
    ZONE_INVALID    = 0xFFFF
} zone_id_t;

/* Zone protection flags */
typedef enum {
    ZONE_PROT_READ   = 0x01,   /* Read access allowed */
    ZONE_PROT_WRITE  = 0x02,   /* Write access allowed */
    ZONE_PROT_EXEC   = 0x04,   /* Execute access allowed */
    ZONE_PROT_CALL   = 0x08,   /* Cross-zone call allowed */
    ZONE_PROT_CAP    = 0x10,   /* Capability transfer allowed */
    ZONE_PROT_DMA    = 0x20,   /* DMA access allowed */
    ZONE_PROT_IRQ    = 0x40,   /* Interrupt handling allowed */
    ZONE_PROT_FULL   = 0xFF    /* All permissions */
} zone_prot_t;

/* Zone descriptor */
typedef struct zone_desc {
    zone_id_t id;               /* Zone identifier */
    uint32_t  protection;       /* Protection flags */
    void     *base_addr;        /* Base virtual address */
    size_t    size;             /* Zone size in bytes */
    cap_id_t  zone_cap;         /* Zone capability */
    uint32_t  owner_pid;        /* Owner process ID */
    struct {
        uint8_t isolated : 1;   /* Zone is isolated */
        uint8_t active   : 1;   /* Zone is active */
        uint8_t locked   : 1;   /* Zone is locked */
        uint8_t quantum  : 1;   /* Quantum-safe crypto */
        uint8_t reserved : 4;
    } flags;
} zone_desc_t;

/* Zone transition context */
typedef struct zone_transition {
    zone_id_t from_zone;        /* Source zone */
    zone_id_t to_zone;          /* Destination zone */
    cap_id_t  transition_cap;   /* Capability authorizing transition */
    uint64_t  timestamp;        /* Transition timestamp */
    uint32_t  saved_state[16];  /* Saved register state */
} zone_transition_t;

/* Zone boundary check result */
typedef enum {
    ZONE_CHECK_OK,              /* Access allowed */
    ZONE_CHECK_DENIED,          /* Access denied */
    ZONE_CHECK_CAP_REQUIRED,    /* Capability required */
    ZONE_CHECK_INVALID_ZONE,    /* Invalid zone */
    ZONE_CHECK_BOUNDARY_VIOLATION /* Boundary violation */
} zone_check_result_t;

/*
 * Zone isolation API
 */

/* Initialize zone isolation subsystem */
void zone_isolation_init(void);

/* Register a new zone */
int zone_register(zone_id_t id, void *base, size_t size, uint32_t prot);

/* Unregister a zone */
int zone_unregister(zone_id_t id);

/* Check if an address belongs to a zone */
zone_id_t zone_get_id(void *addr);

/* Validate cross-zone access */
zone_check_result_t zone_check_access(zone_id_t from, zone_id_t to, 
                                      uint32_t requested_prot, cap_id_t cap);

/* Perform zone transition with capability check */
int zone_transition(zone_id_t target, cap_id_t cap, zone_transition_t *ctx);

/* Lock a zone (prevent modifications) */
int zone_lock(zone_id_t id);

/* Unlock a zone */
int zone_unlock(zone_id_t id);

/* Get zone descriptor */
zone_desc_t *zone_get_desc(zone_id_t id);

/* Verify zone isolation integrity */
bool zone_verify_isolation(void);

/*
 * Compile-time zone boundary enforcement macros
 */

/* Mark a function as kernel-zone only */
#define KERNEL_ZONE_ONLY __attribute__((section(".kernel.text")))

/* Mark a function as LibOS-zone accessible */
#define LIBOS_ZONE __attribute__((section(".libos.text")))

/* Mark a function as application-zone accessible */
#define APP_ZONE __attribute__((section(".app.text")))

/* Static assertion for zone boundary */
#define ASSERT_ZONE_BOUNDARY(zone) \
    _Static_assert(__builtin_constant_p(zone), \
                   "Zone must be compile-time constant")

/* Enforce capability requirement for cross-zone call */
#define REQUIRE_CAP(cap_type) \
    __attribute__((annotate("requires_capability:" #cap_type)))

/* Mark data as zone-local (no cross-zone sharing) */
#define ZONE_LOCAL __attribute__((section(".zone_local")))

/*
 * Runtime zone verification
 */

/* Verify caller is in expected zone */
static inline bool verify_caller_zone(zone_id_t expected) {
    void *caller = __builtin_return_address(0);
    return zone_get_id(caller) == expected;
}

/* Verify data pointer is in expected zone */
static inline bool verify_data_zone(void *ptr, zone_id_t expected) {
    return zone_get_id(ptr) == expected;
}

/*
 * Zone-specific memory allocation
 */

/* Allocate memory in specific zone */
void *zone_malloc(zone_id_t zone, size_t size);

/* Free zone-allocated memory */
void zone_free(zone_id_t zone, void *ptr);

/* Map memory between zones (requires capability) */
void *zone_map(zone_id_t from, zone_id_t to, void *addr, size_t size, cap_id_t cap);

/* Unmap cross-zone mapping */
int zone_unmap(void *addr, size_t size);

/*
 * Zone statistics and debugging
 */

typedef struct zone_stats {
    uint64_t transitions_in;    /* Transitions into zone */
    uint64_t transitions_out;   /* Transitions out of zone */
    uint64_t access_violations; /* Access violations */
    uint64_t cap_checks;        /* Capability checks performed */
    uint64_t cap_failures;      /* Capability check failures */
} zone_stats_t;

/* Get zone statistics */
zone_stats_t *zone_get_stats(zone_id_t id);

/* Dump zone information (debug) */
void zone_dump_info(zone_id_t id);

#ifdef __cplusplus
}
#endif
/**
 * @file reincarnation_server.h
 * @brief Process Resurrection Server - ExoV6 Cleanroom Implementation
 * 
 * Inspired by MINIX3's Reincarnation Server (RS) but redesigned for
 * exokernel architecture with capability-based process resurrection.
 * 
 * Key Features:
 * - Automatic process resurrection after crashes
 * - State preservation and restoration via capabilities
 * - Integration with exokernel capability system
 * - Fault isolation and recovery policies
 * - Service dependency tracking
 * 
 * Design Philosophy:
 * Unlike MINIX3's monolithic RS, this implementation uses:
 * - Capability-based resource tracking
 * - Exokernel-style direct hardware access delegation
 * - Library OS integration for policy decisions
 * - Zero-copy state preservation
 */

#ifndef REINCARNATION_SERVER_H
#define REINCARNATION_SERVER_H

#include <stdint.h>
#include <stdbool.h>
#include "types.h"
#include "cap.h"
#include "exo.h"

#ifdef __cplusplus
extern "C" {
#endif

/* ============================================================================
 * Service State and Configuration
 * ============================================================================ */

#define RS_MAX_SERVICES     64      /* Maximum supervised services */
#define RS_MAX_RESTARTS     5       /* Max restart attempts */
#define RS_RESTART_WINDOW   60000   /* Time window for restart limit (ms) */
#define RS_MAX_DEPS         16      /* Max service dependencies */

/**
 * Service states in resurrection lifecycle
 */
typedef enum {
    RS_STATE_DEAD = 0,          /* Not running, not scheduled */
    RS_STATE_INITIALIZING,      /* Starting up, not ready */
    RS_STATE_ALIVE,             /* Running normally */
    RS_STATE_CRASHED,           /* Detected crash, pending restart */
    RS_STATE_RESTARTING,        /* In process of restarting */
    RS_STATE_SUSPENDED,         /* Administratively stopped */
    RS_STATE_ZOMBIE,            /* Waiting for cleanup */
} rs_state_t;

/**
 * Restart policy for service resurrection
 */
typedef enum {
    RS_POLICY_NEVER = 0,        /* Never restart automatically */
    RS_POLICY_ONCE,             /* Restart once, then give up */
    RS_POLICY_ALWAYS,           /* Always restart on failure */
    RS_POLICY_ON_FAILURE,       /* Restart only if exit status != 0 */
} rs_policy_t;

/**
 * Service descriptor - tracks one supervised service
 */
typedef struct rs_service {
    /* Identity */
    uint32_t service_id;        /* Unique service identifier */
    char name[32];              /* Service name */
    
    /* Process information */
    pid_t pid;                  /* Current process ID (0 if dead) */
    exo_cap proc_cap;           /* Process capability */
    exo_cap mem_cap;            /* Memory capability for state */
    
    /* State management */
    rs_state_t state;           /* Current service state */
    rs_policy_t policy;         /* Restart policy */
    uint32_t restart_count;     /* Restarts in current window */
    uint64_t last_restart_time; /* Timestamp of last restart */
    uint64_t crash_time;        /* Timestamp of last crash */
    int exit_status;            /* Last exit status */
    
    /* Dependencies */
    uint32_t deps[RS_MAX_DEPS]; /* Service IDs this depends on */
    uint32_t num_deps;          /* Number of dependencies */
    
    /* Capabilities for resurrection */
    exo_cap saved_caps[16];     /* Saved capability state */
    uint32_t num_caps;          /* Number of saved caps */
    
    /* Resource limits */
    uint64_t max_memory;        /* Memory limit */
    uint64_t cpu_quota;         /* CPU time quota */
    
    /* Program information */
    char exec_path[256];        /* Path to executable */
    char *argv[32];             /* Command line arguments */
    char *envp[32];             /* Environment variables */
    
} rs_service_t;

/**
 * Resurrection Server global state
 */
typedef struct rs_server {
    rs_service_t services[RS_MAX_SERVICES];
    uint32_t num_services;
    struct spinlock lock;
    
    /* Statistics */
    uint64_t total_restarts;
    uint64_t total_crashes;
    uint64_t failed_restarts;
    
} rs_server_t;

/* ============================================================================
 * Core Resurrection Functions
 * ============================================================================ */

/**
 * Initialize the resurrection server
 */
int rs_init(void);

/**
 * Register a new service for supervision
 * 
 * @param name Service name
 * @param exec_path Path to executable
 * @param policy Restart policy
 * @param service_id_out Output: assigned service ID
 * @return 0 on success, -1 on error
 */
int rs_register_service(const char *name, const char *exec_path, 
                        rs_policy_t policy, uint32_t *service_id_out);

/**
 * Start a supervised service
 * 
 * @param service_id Service to start
 * @return 0 on success, -1 on error
 */
int rs_start_service(uint32_t service_id);

/**
 * Stop a supervised service
 * 
 * @param service_id Service to stop
 * @return 0 on success, -1 on error
 */
int rs_stop_service(uint32_t service_id);

/**
 * Notify RS of a service crash
 * Called by exception handler or watchdog
 * 
 * @param pid Process ID that crashed
 * @param exit_status Exit status or signal number
 * @return 0 if resurrection started, -1 if policy prevents it
 */
int rs_notify_crash(pid_t pid, int exit_status);

/**
 * Check if a service should be restarted
 * 
 * @param service Service descriptor
 * @return true if restart allowed, false otherwise
 */
bool rs_should_restart(const rs_service_t *service);

/**
 * Perform service resurrection
 * 
 * @param service_id Service to resurrect
 * @return 0 on success, -1 on error
 */
int rs_resurrect(uint32_t service_id);

/* ============================================================================
 * Capability State Management
 * ============================================================================ */

/**
 * Save capability state before crash
 * Called periodically or on checkpoints
 * 
 * @param service_id Service whose state to save
 * @return 0 on success, -1 on error
 */
int rs_save_caps(uint32_t service_id);

/**
 * Restore capability state after resurrection
 * 
 * @param service_id Service whose state to restore
 * @return 0 on success, -1 on error
 */
int rs_restore_caps(uint32_t service_id);

/* ============================================================================
 * Dependency Management
 * ============================================================================ */

/**
 * Add a dependency between services
 * 
 * @param service_id Service that depends
 * @param depends_on Service depended upon
 * @return 0 on success, -1 on error
 */
int rs_add_dependency(uint32_t service_id, uint32_t depends_on);

/**
 * Start all dependencies of a service
 * 
 * @param service_id Service whose dependencies to start
 * @return 0 on success, -1 on error
 */
int rs_start_dependencies(uint32_t service_id);

/* ============================================================================
 * Statistics and Monitoring
 * ============================================================================ */

/**
 * Get service information
 * 
 * @param service_id Service to query
 * @param info_out Output: service information
 * @return 0 on success, -1 on error
 */
int rs_get_service_info(uint32_t service_id, rs_service_t *info_out);

/**
 * List all services
 * 
 * @param services_out Output buffer
 * @param max_services Size of buffer
 * @param count_out Output: number of services returned
 * @return 0 on success, -1 on error
 */
int rs_list_services(rs_service_t *services_out, uint32_t max_services, 
                     uint32_t *count_out);

#ifdef __cplusplus
}
#endif

#endif /* REINCARNATION_SERVER_H */

/**
 * @file reincarnation_server.c
 * @brief Process Resurrection Server Implementation
 * 
 * ExoV6 cleanroom implementation of MINIX3-style process resurrection
 * integrated with exokernel capability system.
 */

#include "reincarnation_server.h"
#include "spinlock.h"
#include "proc.h"
#include "defs.h"
#include "string.h"

/* Global resurrection server state */
static rs_server_t rs_server;

/* Forward declarations */
static rs_service_t* rs_find_service_by_id(uint32_t service_id);
static rs_service_t* rs_find_service_by_pid(pid_t pid);
static uint64_t rs_get_time_ms(void);
static int rs_exec_service(rs_service_t *service);

/**
 * Initialize the resurrection server
 */
int rs_init(void) {
    memset(&rs_server, 0, sizeof(rs_server));
    initlock(&rs_server.lock, "resurrection_server");
    
    /* Initialize all services to DEAD state */
    for (uint32_t i = 0; i < RS_MAX_SERVICES; i++) {
        rs_server.services[i].state = RS_STATE_DEAD;
        rs_server.services[i].service_id = i;
    }
    
    rs_server.num_services = 0;
    rs_server.total_restarts = 0;
    rs_server.total_crashes = 0;
    rs_server.failed_restarts = 0;
    
    cprintf("RS: Resurrection Server initialized\n");
    return 0;
}

/**
 * Register a new service for supervision
 */
int rs_register_service(const char *name, const char *exec_path,
                        rs_policy_t policy, uint32_t *service_id_out) {
    if (!name || !exec_path || !service_id_out) {
        return -1;
    }
    
    acquire(&rs_server.lock);
    
    /* Find free slot */
    if (rs_server.num_services >= RS_MAX_SERVICES) {
        release(&rs_server.lock);
        return -1;
    }
    
    /* Find first dead service slot */
    rs_service_t *service = NULL;
    for (uint32_t i = 0; i < RS_MAX_SERVICES; i++) {
        if (rs_server.services[i].state == RS_STATE_DEAD) {
            service = &rs_server.services[i];
            break;
        }
    }
    
    if (!service) {
        release(&rs_server.lock);
        return -1;
    }
    
    /* Initialize service */
    memset(service, 0, sizeof(*service));
    service->state = RS_STATE_DEAD;
    service->policy = policy;
    strncpy(service->name, name, sizeof(service->name) - 1);
    strncpy(service->exec_path, exec_path, sizeof(service->exec_path) - 1);
    
    /* Default resource limits */
    service->max_memory = 64 * 1024 * 1024;  /* 64 MB default */
    service->cpu_quota = 1000;  /* 1000ms default */
    
    *service_id_out = service->service_id;
    rs_server.num_services++;
    
    release(&rs_server.lock);
    
    cprintf("RS: Registered service '%s' (ID %d)\n", name, service->service_id);
    return 0;
}

/**
 * Start a supervised service
 */
int rs_start_service(uint32_t service_id) {
    acquire(&rs_server.lock);
    
    rs_service_t *service = rs_find_service_by_id(service_id);
    if (!service || service->state == RS_STATE_ALIVE) {
        release(&rs_server.lock);
        return -1;
    }
    
    /* Start dependencies first */
    for (uint32_t i = 0; i < service->num_deps; i++) {
        rs_service_t *dep = rs_find_service_by_id(service->deps[i]);
        if (dep && dep->state != RS_STATE_ALIVE) {
            /* Recursively start dependency */
            release(&rs_server.lock);
            if (rs_start_service(dep->service_id) != 0) {
                return -1;
            }
            acquire(&rs_server.lock);
        }
    }
    
    service->state = RS_STATE_INITIALIZING;
    
    /* Execute the service */
    int result = rs_exec_service(service);
    
    if (result == 0) {
        service->state = RS_STATE_ALIVE;
        service->restart_count = 0;
        service->last_restart_time = rs_get_time_ms();
        cprintf("RS: Started service '%s' (PID %d)\n", service->name, service->pid);
    } else {
        service->state = RS_STATE_DEAD;
        cprintf("RS: Failed to start service '%s'\n", service->name);
    }
    
    release(&rs_server.lock);
    return result;
}

/**
 * Stop a supervised service
 */
int rs_stop_service(uint32_t service_id) {
    acquire(&rs_server.lock);
    
    rs_service_t *service = rs_find_service_by_id(service_id);
    if (!service || service->state == RS_STATE_DEAD) {
        release(&rs_server.lock);
        return -1;
    }
    
    /* Send termination signal */
    if (service->pid > 0) {
        /* TODO: Implement process termination via exokernel */
        /* For now, just mark as suspended */
    }
    
    service->state = RS_STATE_SUSPENDED;
    service->pid = 0;
    
    cprintf("RS: Stopped service '%s'\n", service->name);
    
    release(&rs_server.lock);
    return 0;
}

/**
 * Notify RS of a service crash
 */
int rs_notify_crash(pid_t pid, int exit_status) {
    acquire(&rs_server.lock);
    
    rs_service_t *service = rs_find_service_by_pid(pid);
    if (!service) {
        release(&rs_server.lock);
        return -1;
    }
    
    cprintf("RS: Service '%s' (PID %d) crashed with status %d\n",
            service->name, pid, exit_status);
    
    service->state = RS_STATE_CRASHED;
    service->exit_status = exit_status;
    service->crash_time = rs_get_time_ms();
    service->pid = 0;
    
    rs_server.total_crashes++;
    
    /* Check if we should restart */
    if (rs_should_restart(service)) {
        release(&rs_server.lock);
        return rs_resurrect(service->service_id);
    }
    
    release(&rs_server.lock);
    return -1;
}

/**
 * Check if a service should be restarted
 */
bool rs_should_restart(const rs_service_t *service) {
    if (!service) {
        return false;
    }
    
    /* Check policy */
    switch (service->policy) {
        case RS_POLICY_NEVER:
            return false;
            
        case RS_POLICY_ONCE:
            return service->restart_count == 0;
            
        case RS_POLICY_ALWAYS:
            break;
            
        case RS_POLICY_ON_FAILURE:
            if (service->exit_status == 0) {
                return false;
            }
            break;
    }
    
    /* Check restart rate limit */
    uint64_t now = rs_get_time_ms();
    uint64_t window_start = now - RS_RESTART_WINDOW;
    
    if (service->last_restart_time > window_start) {
        /* Within restart window - check count */
        if (service->restart_count >= RS_MAX_RESTARTS) {
            cprintf("RS: Service '%s' exceeded restart limit\n", service->name);
            return false;
        }
    }
    
    return true;
}

/**
 * Perform service resurrection
 */
int rs_resurrect(uint32_t service_id) {
    acquire(&rs_server.lock);
    
    rs_service_t *service = rs_find_service_by_id(service_id);
    if (!service) {
        release(&rs_server.lock);
        return -1;
    }
    
    cprintf("RS: Resurrecting service '%s'...\n", service->name);
    
    service->state = RS_STATE_RESTARTING;
    service->restart_count++;
    service->last_restart_time = rs_get_time_ms();
    
    /* Restore saved capability state */
    if (rs_restore_caps(service_id) != 0) {
        cprintf("RS: Failed to restore capabilities for '%s'\n", service->name);
    }
    
    /* Re-execute the service */
    int result = rs_exec_service(service);
    
    if (result == 0) {
        service->state = RS_STATE_ALIVE;
        rs_server.total_restarts++;
        cprintf("RS: Resurrected service '%s' (PID %d)\n", 
                service->name, service->pid);
    } else {
        service->state = RS_STATE_DEAD;
        rs_server.failed_restarts++;
        cprintf("RS: Failed to resurrect service '%s'\n", service->name);
    }
    
    release(&rs_server.lock);
    return result;
}

/**
 * Save capability state
 */
int rs_save_caps(uint32_t service_id) {
    rs_service_t *service = rs_find_service_by_id(service_id);
    if (!service || service->state != RS_STATE_ALIVE) {
        return -1;
    }
    
    /* TODO: Implement capability snapshotting */
    /* This would enumerate all capabilities held by the process
     * and save them for later restoration */
    
    service->num_caps = 0;  /* Placeholder */
    
    return 0;
}

/**
 * Restore capability state
 */
int rs_restore_caps(uint32_t service_id) {
    rs_service_t *service = rs_find_service_by_id(service_id);
    if (!service) {
        return -1;
    }
    
    /* TODO: Implement capability restoration */
    /* This would grant the resurrected process the same
     * capabilities it had before the crash */
    
    for (uint32_t i = 0; i < service->num_caps; i++) {
        /* Restore each capability */
        (void)service->saved_caps[i];  /* Placeholder */
    }
    
    return 0;
}

/**
 * Add a dependency between services
 */
int rs_add_dependency(uint32_t service_id, uint32_t depends_on) {
    acquire(&rs_server.lock);
    
    rs_service_t *service = rs_find_service_by_id(service_id);
    if (!service || service->num_deps >= RS_MAX_DEPS) {
        release(&rs_server.lock);
        return -1;
    }
    
    /* Check for circular dependencies (simple check) */
    if (service_id == depends_on) {
        release(&rs_server.lock);
        return -1;
    }
    
    service->deps[service->num_deps++] = depends_on;
    
    release(&rs_server.lock);
    return 0;
}

/**
 * Get service information
 */
int rs_get_service_info(uint32_t service_id, rs_service_t *info_out) {
    if (!info_out) {
        return -1;
    }
    
    acquire(&rs_server.lock);
    
    rs_service_t *service = rs_find_service_by_id(service_id);
    if (!service) {
        release(&rs_server.lock);
        return -1;
    }
    
    memcpy(info_out, service, sizeof(*info_out));
    
    release(&rs_server.lock);
    return 0;
}

/**
 * List all services
 */
int rs_list_services(rs_service_t *services_out, uint32_t max_services,
                     uint32_t *count_out) {
    if (!services_out || !count_out) {
        return -1;
    }
    
    acquire(&rs_server.lock);
    
    uint32_t count = 0;
    for (uint32_t i = 0; i < RS_MAX_SERVICES && count < max_services; i++) {
        if (rs_server.services[i].state != RS_STATE_DEAD) {
            memcpy(&services_out[count], &rs_server.services[i],
                   sizeof(rs_service_t));
            count++;
        }
    }
    
    *count_out = count;
    
    release(&rs_server.lock);
    return 0;
}

/* ============================================================================
 * Helper Functions
 * ============================================================================ */

static rs_service_t* rs_find_service_by_id(uint32_t service_id) {
    if (service_id >= RS_MAX_SERVICES) {
        return NULL;
    }
    
    rs_service_t *service = &rs_server.services[service_id];
    if (service->state == RS_STATE_DEAD && service->service_id != service_id) {
        return NULL;
    }
    
    return service;
}

static rs_service_t* rs_find_service_by_pid(pid_t pid) {
    for (uint32_t i = 0; i < RS_MAX_SERVICES; i++) {
        if (rs_server.services[i].pid == pid) {
            return &rs_server.services[i];
        }
    }
    return NULL;
}

static uint64_t rs_get_time_ms(void) {
    /* TODO: Implement proper time source */
    /* For now, return a placeholder */
    return 0;
}

static int rs_exec_service(rs_service_t *service) {
    /* TODO: Implement process execution via exokernel */
    /* This would:
     * 1. Allocate a new process structure
     * 2. Load the executable from exec_path
     * 3. Set up initial capability environment
     * 4. Transfer control to the new process
     */
    
    /* Placeholder - would call fork/exec equivalent */
    service->pid = 1;  /* Dummy PID */
    
    return 0;  /* Success */
}

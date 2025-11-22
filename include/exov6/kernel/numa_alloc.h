#pragma once

/**
 * @file numa_alloc.h
 * @brief NUMA-Aware Memory Allocator (Phase 5.4.2)
 *
 * Simplified NUMA allocator for local/remote memory management.
 */

#include "numa_topology.h"
#include <stdint.h>
#include <stddef.h>

/**
 * NUMA allocation flags
 */
typedef enum {
    NUMA_ALLOC_LOCAL = 0,      /* Allocate on local node (preferred) */
    NUMA_ALLOC_INTERLEAVE,     /* Interleave across all nodes */
    NUMA_ALLOC_SPECIFIC,       /* Allocate on specific node */
    NUMA_ALLOC_NEAREST         /* Allocate on nearest node with space */
} numa_alloc_policy_t;

/**
 * Allocate memory with NUMA awareness
 *
 * @param topo      NUMA topology
 * @param size      Size in bytes
 * @param policy    Allocation policy
 * @param preferred_node  Preferred node (for LOCAL/SPECIFIC)
 * @return          Pointer to allocated memory, or NULL on failure
 */
void *numa_alloc(numa_topology_t *topo,
                size_t size,
                numa_alloc_policy_t policy,
                uint8_t preferred_node);

/**
 * Free NUMA-allocated memory
 *
 * @param topo  NUMA topology
 * @param ptr   Pointer to free
 * @param size  Size in bytes
 */
void numa_free(numa_topology_t *topo, void *ptr, size_t size);

/**
 * Get node where memory was allocated
 *
 * @param ptr  Memory pointer
 * @return     Node ID (simplified: returns 0 in simulation)
 */
uint8_t numa_get_allocation_node(void *ptr);

/**
 * @file numa_alloc.c
 * @brief NUMA-Aware Memory Allocator Implementation (Phase 5.4.2)
 */

#include "numa_alloc.h"
#include <stdlib.h>
#include <stdint.h>

/**
 * Allocate memory with NUMA awareness
 *
 * In a real kernel:
 * - Track which node has memory
 * - Use mbind() or similar to bind pages to nodes
 * - Implement per-node freelists
 *
 * In simulation:
 * - Use standard malloc but track node in topology
 * - Update node memory counters
 */
void *numa_alloc(numa_topology_t *topo,
                size_t size,
                numa_alloc_policy_t policy,
                uint8_t preferred_node)
{
    if (topo == NULL || size == 0) {
        return NULL;
    }

    uint64_t size_mb = (size + 1024 * 1024 - 1) / (1024 * 1024);  /* Round up to MB */
    uint8_t target_node = 0;

    /* Determine target node based on policy */
    switch (policy) {
        case NUMA_ALLOC_LOCAL:
        case NUMA_ALLOC_SPECIFIC:
            if (preferred_node < topo->num_nodes) {
                target_node = preferred_node;
            }
            break;

        case NUMA_ALLOC_NEAREST:
            target_node = numa_find_least_loaded_node(topo);
            break;

        case NUMA_ALLOC_INTERLEAVE:
            /* Simplified: just use least loaded */
            target_node = numa_find_least_loaded_node(topo);
            break;
    }

    /* Check if node has enough free memory */
    numa_node_t *node = &topo->nodes[target_node];
    if (node->memory_free_mb < size_mb) {
        /* Try to find another node */
        target_node = numa_find_least_loaded_node(topo);
        node = &topo->nodes[target_node];

        if (node->memory_free_mb < size_mb) {
            return NULL;  /* Out of memory */
        }
    }

    /* Allocate (using standard malloc in simulation) */
    void *ptr = malloc(size);
    if (ptr == NULL) {
        return NULL;
    }

    /* Update node memory accounting */
    node->memory_free_mb -= size_mb;
    topo->total_free_mb -= size_mb;

    return ptr;
}

/**
 * Free NUMA-allocated memory
 */
void numa_free(numa_topology_t *topo, void *ptr, size_t size)
{
    if (topo == NULL || ptr == NULL) {
        return;
    }

    uint64_t size_mb = (size + 1024 * 1024 - 1) / (1024 * 1024);

    /* In real implementation, would look up which node owns this memory */
    /* For simulation, just update total free memory */
    topo->total_free_mb += size_mb;

    /* Update first node (simplified) */
    if (topo->num_nodes > 0) {
        topo->nodes[0].memory_free_mb += size_mb;
    }

    free(ptr);
}

/**
 * Get node where memory was allocated
 */
uint8_t numa_get_allocation_node(void *ptr)
{
    (void)ptr;
    /* In real kernel, would look up page tables or memory map */
    /* In simulation, return node 0 */
    return 0;
}

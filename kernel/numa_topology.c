/**
 * @file numa_topology.c
 * @brief NUMA Topology Implementation (Phase 5.4.1)
 */

#include "numa_topology.h"
#include "printf.h"
#include <string.h>

/*******************************************************************************
 * TOPOLOGY DETECTION & INITIALIZATION
 ******************************************************************************/

/**
 * Detect hardware NUMA topology
 *
 * In userspace simulation, this always returns false.
 * Real kernel would parse /proc/cpuinfo, /sys/devices/system/node, etc.
 */
bool numa_topology_detect(numa_topology_t *topo)
{
    (void)topo;

    /* In simulation environment, no hardware detection available */
    return false;
}

/**
 * Simulate NUMA topology
 */
int numa_topology_simulate(numa_topology_t *topo,
                           uint8_t num_nodes,
                           uint8_t cpus_per_node,
                           uint64_t memory_per_node_mb)
{
    if (topo == NULL) {
        return -1;
    }

    if (num_nodes > MAX_NUMA_NODES || num_nodes == 0) {
        return -1;
    }

    if (cpus_per_node > MAX_CPUS_PER_NODE || cpus_per_node == 0) {
        return -1;
    }

    memset(topo, 0, sizeof(numa_topology_t));

    topo->num_nodes = num_nodes;
    topo->total_cpus = num_nodes * cpus_per_node;
    topo->total_memory_mb = num_nodes * memory_per_node_mb;
    topo->total_free_mb = topo->total_memory_mb;
    topo->detected = false;
    topo->simulated = true;

    /* Initialize each node */
    uint8_t next_cpu_id = 0;

    for (uint8_t node_id = 0; node_id < num_nodes; node_id++) {
        numa_node_t *node = &topo->nodes[node_id];

        node->node_id = node_id;
        node->num_cpus = cpus_per_node;
        node->memory_size_mb = memory_per_node_mb;
        node->memory_free_mb = memory_per_node_mb;

        /* Assign CPUs to this node */
        for (uint8_t i = 0; i < cpus_per_node; i++) {
            node->cpu_ids[i] = next_cpu_id;
            topo->cpu_to_node[next_cpu_id] = node_id;
            next_cpu_id++;
        }

        /* Build distance matrix */
        for (uint8_t other_node = 0; other_node < num_nodes; other_node++) {
            if (other_node == node_id) {
                /* Local access */
                node->distance[other_node] = 10;
            } else {
                /* Remote access - distance based on topology */
                uint8_t node_diff = (other_node > node_id) ?
                                   (other_node - node_id) :
                                   (node_id - other_node);

                /* Simple ring topology distance model */
                if (node_diff == 1 || node_diff == (num_nodes - 1)) {
                    /* Adjacent nodes (1-hop) */
                    node->distance[other_node] = 20;
                } else if (node_diff == 2 || node_diff == (num_nodes - 2)) {
                    /* 2-hop */
                    node->distance[other_node] = 30;
                } else {
                    /* Further hops */
                    node->distance[other_node] = 40;
                }
            }
        }
    }

    return 0;
}

/**
 * Initialize UMA topology
 */
int numa_topology_init_uma(numa_topology_t *topo,
                           uint8_t num_cpus,
                           uint64_t memory_mb)
{
    /* UMA is just a single NUMA node */
    return numa_topology_simulate(topo, 1, num_cpus, memory_mb);
}

/*******************************************************************************
 * TOPOLOGY QUERIES
 ******************************************************************************/

/**
 * Get NUMA node for CPU
 */
uint8_t numa_get_cpu_node(const numa_topology_t *topo, uint8_t cpu_id)
{
    if (topo == NULL || cpu_id >= topo->total_cpus) {
        return 0;
    }

    return topo->cpu_to_node[cpu_id];
}

/**
 * Get CPUs in a NUMA node
 */
uint8_t numa_get_node_cpus(const numa_topology_t *topo,
                          uint8_t node_id,
                          uint8_t *cpu_list,
                          uint8_t max_cpus)
{
    if (topo == NULL || node_id >= topo->num_nodes || cpu_list == NULL) {
        return 0;
    }

    const numa_node_t *node = &topo->nodes[node_id];
    uint8_t count = (node->num_cpus < max_cpus) ? node->num_cpus : max_cpus;

    for (uint8_t i = 0; i < count; i++) {
        cpu_list[i] = node->cpu_ids[i];
    }

    return count;
}

/**
 * Get distance between two nodes
 */
uint8_t numa_get_distance(const numa_topology_t *topo,
                         uint8_t from_node,
                         uint8_t to_node)
{
    if (topo == NULL || from_node >= topo->num_nodes || to_node >= topo->num_nodes) {
        return 10;  /* Default to local */
    }

    return topo->nodes[from_node].distance[to_node];
}

/**
 * Check if two CPUs are on the same NUMA node
 */
bool numa_cpus_are_local(const numa_topology_t *topo,
                        uint8_t cpu1,
                        uint8_t cpu2)
{
    if (topo == NULL) {
        return true;
    }

    return numa_get_cpu_node(topo, cpu1) == numa_get_cpu_node(topo, cpu2);
}

/**
 * Get local memory size for node
 */
uint64_t numa_get_node_memory(const numa_topology_t *topo, uint8_t node_id)
{
    if (topo == NULL || node_id >= topo->num_nodes) {
        return 0;
    }

    return topo->nodes[node_id].memory_size_mb;
}

/*******************************************************************************
 * AFFINITY HINTS
 ******************************************************************************/

/**
 * Find least loaded NUMA node
 */
uint8_t numa_find_least_loaded_node(const numa_topology_t *topo)
{
    if (topo == NULL || topo->num_nodes == 0) {
        return 0;
    }

    uint8_t best_node = 0;
    uint64_t max_free = topo->nodes[0].memory_free_mb;

    for (uint8_t node_id = 1; node_id < topo->num_nodes; node_id++) {
        if (topo->nodes[node_id].memory_free_mb > max_free) {
            max_free = topo->nodes[node_id].memory_free_mb;
            best_node = node_id;
        }
    }

    return best_node;
}

/**
 * Find nearest node to given node
 */
uint8_t numa_find_nearest_node(const numa_topology_t *topo,
                               uint8_t from_node,
                               bool exclude_self)
{
    if (topo == NULL || from_node >= topo->num_nodes) {
        return 0;
    }

    if (topo->num_nodes == 1) {
        return 0;
    }

    uint8_t nearest = from_node;
    uint8_t min_distance = 255;

    for (uint8_t node_id = 0; node_id < topo->num_nodes; node_id++) {
        if (exclude_self && node_id == from_node) {
            continue;
        }

        uint8_t dist = topo->nodes[from_node].distance[node_id];
        if (dist < min_distance) {
            min_distance = dist;
            nearest = node_id;
        }
    }

    return nearest;
}

/*******************************************************************************
 * DEBUGGING & VISUALIZATION
 ******************************************************************************/

/**
 * Print topology summary
 */
void numa_print_topology(const numa_topology_t *topo)
{
    if (topo == NULL) {
        return;
    }

    printf("=== NUMA Topology ===\n");
    printf("Nodes:       %u\n", topo->num_nodes);
    printf("Total CPUs:  %u\n", topo->total_cpus);
    printf("Total Memory: %lu MB\n", topo->total_memory_mb);
    printf("Mode:        %s\n", topo->simulated ? "Simulated" : "Detected");

    if (topo->num_nodes == 1) {
        printf("Type:        UMA (Uniform Memory Access)\n");
    } else {
        printf("Type:        NUMA (%u nodes)\n", topo->num_nodes);
    }

    printf("\n");

    for (uint8_t node_id = 0; node_id < topo->num_nodes; node_id++) {
        const numa_node_t *node = &topo->nodes[node_id];

        printf("Node %u:\n", node_id);
        printf("  CPUs:   %u (", node->num_cpus);
        for (uint8_t i = 0; i < node->num_cpus; i++) {
            printf("%u%s", node->cpu_ids[i],
                   (i < node->num_cpus - 1) ? "," : "");
        }
        printf(")\n");
        printf("  Memory: %lu MB (%lu free)\n",
               node->memory_size_mb, node->memory_free_mb);
        printf("\n");
    }
}

/**
 * Print distance matrix
 */
void numa_print_distance_matrix(const numa_topology_t *topo)
{
    if (topo == NULL) {
        return;
    }

    printf("=== NUMA Distance Matrix ===\n");
    printf("(10 = local, 20 = 1-hop, 30 = 2-hop, 40+ = far)\n\n");

    /* Header */
    printf("    ");
    for (uint8_t col = 0; col < topo->num_nodes; col++) {
        printf(" N%u", col);
    }
    printf("\n");

    /* Rows */
    for (uint8_t row = 0; row < topo->num_nodes; row++) {
        printf("N%u: ", row);
        for (uint8_t col = 0; col < topo->num_nodes; col++) {
            printf(" %2u", topo->nodes[row].distance[col]);
        }
        printf("\n");
    }
    printf("\n");
}

/**
 * Get topology statistics
 */
void numa_get_stats(const numa_topology_t *topo, numa_stats_t *stats)
{
    if (topo == NULL || stats == NULL) {
        return;
    }

    memset(stats, 0, sizeof(numa_stats_t));

    stats->num_nodes = topo->num_nodes;
    stats->total_cpus = topo->total_cpus;
    stats->total_memory_mb = topo->total_memory_mb;
    stats->total_free_mb = topo->total_free_mb;

    if (topo->num_nodes > 0) {
        stats->avg_cpus_per_node = topo->total_cpus / topo->num_nodes;
        stats->avg_memory_per_node_mb = topo->total_memory_mb / topo->num_nodes;
    }

    /* Find max distance */
    uint8_t max_dist = 0;
    for (uint8_t i = 0; i < topo->num_nodes; i++) {
        for (uint8_t j = 0; j < topo->num_nodes; j++) {
            if (topo->nodes[i].distance[j] > max_dist) {
                max_dist = topo->nodes[i].distance[j];
            }
        }
    }
    stats->max_distance = max_dist;

    stats->is_uniform = (topo->num_nodes == 1);
}

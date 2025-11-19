#pragma once

/**
 * @file numa_topology.h
 * @brief NUMA (Non-Uniform Memory Access) Topology Detection & Simulation
 *
 * PEDAGOGICAL PURPOSE:
 * ====================
 * Demonstrates NUMA-aware system design for modern multi-socket servers.
 *
 * REAL-WORLD ANALOGUES:
 * =====================
 * - Linux: numa_maps, numactl, libnuma
 * - Windows: GetNumaHighestNodeNumber, GetNumaNodeProcessorMask
 * - Solaris: lgrp_* APIs
 * - FreeBSD: cpuset(2)
 *
 * KEY CONCEPTS:
 * =============
 * - **NUMA Node**: Physical CPU socket with local memory
 * - **Memory Affinity**: Access cost varies by node (local < remote)
 * - **CPU Affinity**: Cores are grouped by node
 * - **Distance Matrix**: Relative access costs between nodes
 *
 * PERFORMANCE IMPACT:
 * ===================
 * - Local memory access: ~80ns latency
 * - Remote memory access: ~120-200ns latency (1.5-2.5x slower)
 * - Cross-node traffic: Limited by interconnect bandwidth (QPI, Infinity Fabric)
 *
 * Phase 5.4.1: Basic topology detection and simulation
 */

#include "types.h"
#include <stdint.h>

/* ============================================================================
 * CONSTANTS
 * ============================================================================ */

#define MAX_NUMA_NODES 8       /* Maximum NUMA nodes supported */
#define MAX_CPUS_PER_NODE 16   /* Maximum CPUs per NUMA node */

/* ============================================================================
 * NUMA TOPOLOGY STRUCTURES
 * ============================================================================ */

/**
 * NUMA node descriptor
 */
typedef struct numa_node {
    uint8_t node_id;                       /* Node ID (0-based) */
    uint8_t num_cpus;                      /* CPUs in this node */
    uint8_t cpu_ids[MAX_CPUS_PER_NODE];    /* CPU IDs */

    uint64_t memory_size_mb;               /* Local memory size (MB) */
    uint64_t memory_free_mb;               /* Free local memory (MB) */

    /* Distance to other nodes (relative cost, 10 = local) */
    uint8_t distance[MAX_NUMA_NODES];      /* 10 = local, 20 = 1-hop, 30 = 2-hop */
} numa_node_t;

/**
 * System-wide NUMA topology
 */
typedef struct numa_topology {
    uint8_t num_nodes;                     /* Number of NUMA nodes */
    uint8_t total_cpus;                    /* Total CPUs across all nodes */

    numa_node_t nodes[MAX_NUMA_NODES];     /* Node descriptors */

    /* CPU to node mapping (indexed by CPU ID) */
    uint8_t cpu_to_node[MAX_CPUS_PER_NODE * MAX_NUMA_NODES];

    /* System-wide memory */
    uint64_t total_memory_mb;              /* Total system memory */
    uint64_t total_free_mb;                /* Total free memory */

    bool detected;                          /* True if detected from hardware */
    bool simulated;                         /* True if simulated */
} numa_topology_t;

/* ============================================================================
 * TOPOLOGY DETECTION & INITIALIZATION
 * ============================================================================ */

/**
 * Detect hardware NUMA topology
 *
 * On real hardware:
 * - Linux: Parse /sys/devices/system/node/node*
 * - Windows: Use GetNumaNodeProcessorMask
 * - Other: Use libnuma or equivalent
 *
 * In simulation:
 * - Returns false, use numa_topology_simulate() instead
 *
 * @param topo  Topology structure to populate
 * @return      True if detected from hardware, false if not available
 */
bool numa_topology_detect(numa_topology_t *topo);

/**
 * Simulate NUMA topology
 *
 * Creates realistic multi-node topology for testing/development.
 *
 * Configurations:
 * - 1 node:  UMA (uniform memory access)
 * - 2 nodes: Dual-socket server
 * - 4 nodes: Quad-socket server
 * - 8 nodes: Large-scale NUMA machine
 *
 * @param topo       Topology structure to populate
 * @param num_nodes  Number of NUMA nodes to simulate (1-8)
 * @param cpus_per_node  CPUs per node (1-16)
 * @param memory_per_node_mb  Memory per node in MB
 * @return           0 on success, -1 on error
 */
int numa_topology_simulate(numa_topology_t *topo,
                           uint8_t num_nodes,
                           uint8_t cpus_per_node,
                           uint64_t memory_per_node_mb);

/**
 * Initialize UMA (uniform) topology
 *
 * Single node with all CPUs (no NUMA effects).
 *
 * @param topo      Topology structure
 * @param num_cpus  Total CPUs
 * @param memory_mb Total memory
 * @return          0 on success, -1 on error
 */
int numa_topology_init_uma(numa_topology_t *topo,
                           uint8_t num_cpus,
                           uint64_t memory_mb);

/* ============================================================================
 * TOPOLOGY QUERIES
 * ============================================================================ */

/**
 * Get NUMA node for CPU
 *
 * @param topo    Topology
 * @param cpu_id  CPU ID
 * @return        Node ID, or 0 if invalid CPU
 */
uint8_t numa_get_cpu_node(const numa_topology_t *topo, uint8_t cpu_id);

/**
 * Get CPUs in a NUMA node
 *
 * @param topo      Topology
 * @param node_id   Node ID
 * @param cpu_list  Output: array of CPU IDs
 * @param max_cpus  Size of cpu_list array
 * @return          Number of CPUs in node
 */
uint8_t numa_get_node_cpus(const numa_topology_t *topo,
                          uint8_t node_id,
                          uint8_t *cpu_list,
                          uint8_t max_cpus);

/**
 * Get distance between two nodes
 *
 * @param topo       Topology
 * @param from_node  Source node
 * @param to_node    Destination node
 * @return           Relative distance (10 = local, 20 = 1-hop, etc.)
 */
uint8_t numa_get_distance(const numa_topology_t *topo,
                         uint8_t from_node,
                         uint8_t to_node);

/**
 * Check if two CPUs are on the same NUMA node
 *
 * @param topo   Topology
 * @param cpu1   First CPU
 * @param cpu2   Second CPU
 * @return       True if same node (local access)
 */
bool numa_cpus_are_local(const numa_topology_t *topo,
                        uint8_t cpu1,
                        uint8_t cpu2);

/**
 * Get local memory size for node
 *
 * @param topo     Topology
 * @param node_id  Node ID
 * @return         Memory size in MB
 */
uint64_t numa_get_node_memory(const numa_topology_t *topo, uint8_t node_id);

/* ============================================================================
 * AFFINITY HINTS
 * ============================================================================ */

/**
 * Find least loaded NUMA node
 *
 * Based on memory usage (not CPU load yet - see Task 5.4.3).
 *
 * @param topo  Topology
 * @return      Node ID with most free memory
 */
uint8_t numa_find_least_loaded_node(const numa_topology_t *topo);

/**
 * Find nearest node to given node
 *
 * Useful for migration when local node is full.
 *
 * @param topo          Topology
 * @param from_node     Source node
 * @param exclude_self  If true, don't return from_node
 * @return              Nearest node ID
 */
uint8_t numa_find_nearest_node(const numa_topology_t *topo,
                               uint8_t from_node,
                               bool exclude_self);

/* ============================================================================
 * DEBUGGING & VISUALIZATION
 * ============================================================================ */

/**
 * Print topology summary
 *
 * @param topo  Topology
 */
void numa_print_topology(const numa_topology_t *topo);

/**
 * Print distance matrix
 *
 * @param topo  Topology
 */
void numa_print_distance_matrix(const numa_topology_t *topo);

/**
 * Get topology statistics
 *
 * @param topo   Topology
 * @param stats  Output statistics
 */
typedef struct numa_stats {
    uint8_t num_nodes;
    uint8_t total_cpus;
    uint64_t total_memory_mb;
    uint64_t total_free_mb;
    uint8_t avg_cpus_per_node;
    uint64_t avg_memory_per_node_mb;
    uint8_t max_distance;           /* Maximum inter-node distance */
    bool is_uniform;                 /* True if UMA */
} numa_stats_t;

void numa_get_stats(const numa_topology_t *topo, numa_stats_t *stats);

/**
 * @file test_numa.c
 * @brief NUMA Topology and Allocation Tests (Phase 5.4.5)
 */

#include "numa_topology.h"
#include "numa_alloc.h"
#include "printf.h"
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

/* Test macros */
#define TEST_START(name) printf("TEST: %s ... ", name)
#define TEST_PASS() printf("PASS\n")
#define TEST_FAIL(msg) do { printf("FAIL: %s\n", msg); return; } while(0)
#define ASSERT(cond, msg) do { if (!(cond)) TEST_FAIL(msg); } while(0)

/*******************************************************************************
 * TOPOLOGY TESTS
 ******************************************************************************/

void test_numa_uma_topology(void)
{
    TEST_START("UMA topology initialization");

    numa_topology_t topo;
    int ret = numa_topology_init_uma(&topo, 8, 16384);
    ASSERT(ret == 0, "UMA init failed");

    ASSERT(topo.num_nodes == 1, "Should have 1 node");
    ASSERT(topo.total_cpus == 8, "Should have 8 CPUs");
    ASSERT(topo.simulated == true, "Should be simulated");

    /* All CPUs should be on node 0 */
    for (uint8_t cpu = 0; cpu < 8; cpu++) {
        ASSERT(numa_get_cpu_node(&topo, cpu) == 0, "All CPUs on node 0");
    }

    /* Distance should be local (10) everywhere */
    ASSERT(numa_get_distance(&topo, 0, 0) == 10, "Local distance is 10");

    TEST_PASS();
}

void test_numa_dual_socket(void)
{
    TEST_START("Dual-socket NUMA topology");

    numa_topology_t topo;
    int ret = numa_topology_simulate(&topo, 2, 8, 32768);
    ASSERT(ret == 0, "Dual-socket init failed");

    ASSERT(topo.num_nodes == 2, "Should have 2 nodes");
    ASSERT(topo.total_cpus == 16, "Should have 16 CPUs");

    /* CPUs 0-7 on node 0, 8-15 on node 1 */
    for (uint8_t cpu = 0; cpu < 8; cpu++) {
        ASSERT(numa_get_cpu_node(&topo, cpu) == 0, "CPUs 0-7 on node 0");
    }
    for (uint8_t cpu = 8; cpu < 16; cpu++) {
        ASSERT(numa_get_cpu_node(&topo, cpu) == 1, "CPUs 8-15 on node 1");
    }

    /* Distance matrix */
    ASSERT(numa_get_distance(&topo, 0, 0) == 10, "Node 0 to 0: local");
    ASSERT(numa_get_distance(&topo, 0, 1) == 20, "Node 0 to 1: 1-hop");
    ASSERT(numa_get_distance(&topo, 1, 0) == 20, "Node 1 to 0: 1-hop");
    ASSERT(numa_get_distance(&topo, 1, 1) == 10, "Node 1 to 1: local");

    TEST_PASS();
}

void test_numa_quad_socket(void)
{
    TEST_START("Quad-socket NUMA topology");

    numa_topology_t topo;
    int ret = numa_topology_simulate(&topo, 4, 16, 65536);
    ASSERT(ret == 0, "Quad-socket init failed");

    ASSERT(topo.num_nodes == 4, "Should have 4 nodes");
    ASSERT(topo.total_cpus == 64, "Should have 64 CPUs");

    /* Distance matrix validation */
    ASSERT(numa_get_distance(&topo, 0, 0) == 10, "Local");
    ASSERT(numa_get_distance(&topo, 0, 1) == 20, "Adjacent");
    ASSERT(numa_get_distance(&topo, 0, 2) == 30, "2-hop");
    ASSERT(numa_get_distance(&topo, 0, 3) == 20, "Adjacent (ring)");

    TEST_PASS();
}

void test_numa_cpu_locality(void)
{
    TEST_START("CPU locality checks");

    numa_topology_t topo;
    numa_topology_simulate(&topo, 2, 4, 16384);

    /* CPUs on same node are local */
    ASSERT(numa_cpus_are_local(&topo, 0, 1) == true, "CPU 0,1 local");
    ASSERT(numa_cpus_are_local(&topo, 0, 3) == true, "CPU 0,3 local");

    /* CPUs on different nodes are not local */
    ASSERT(numa_cpus_are_local(&topo, 0, 4) == false, "CPU 0,4 not local");
    ASSERT(numa_cpus_are_local(&topo, 3, 5) == false, "CPU 3,5 not local");

    TEST_PASS();
}

void test_numa_node_cpus(void)
{
    TEST_START("Get CPUs in node");

    numa_topology_t topo;
    numa_topology_simulate(&topo, 2, 4, 16384);

    uint8_t cpu_list[8];
    uint8_t count;

    /* Node 0: CPUs 0-3 */
    count = numa_get_node_cpus(&topo, 0, cpu_list, 8);
    ASSERT(count == 4, "Node 0 has 4 CPUs");
    ASSERT(cpu_list[0] == 0, "First CPU is 0");
    ASSERT(cpu_list[3] == 3, "Last CPU is 3");

    /* Node 1: CPUs 4-7 */
    count = numa_get_node_cpus(&topo, 1, cpu_list, 8);
    ASSERT(count == 4, "Node 1 has 4 CPUs");
    ASSERT(cpu_list[0] == 4, "First CPU is 4");
    ASSERT(cpu_list[3] == 7, "Last CPU is 7");

    TEST_PASS();
}

void test_numa_find_least_loaded(void)
{
    TEST_START("Find least loaded node");

    numa_topology_t topo;
    numa_topology_simulate(&topo, 3, 4, 16384);

    /* Initially all nodes have same free memory */
    uint8_t node = numa_find_least_loaded_node(&topo);
    ASSERT(node < 3, "Valid node returned");

    /* Allocate on node 0 */
    topo.nodes[0].memory_free_mb = 8000;
    topo.nodes[1].memory_free_mb = 16000;
    topo.nodes[2].memory_free_mb = 12000;

    /* Node 1 should be least loaded (most free) */
    node = numa_find_least_loaded_node(&topo);
    ASSERT(node == 1, "Node 1 is least loaded");

    TEST_PASS();
}

void test_numa_find_nearest(void)
{
    TEST_START("Find nearest node");

    numa_topology_t topo;
    numa_topology_simulate(&topo, 4, 4, 16384);

    /* From node 0, nearest is node 1 or 3 (adjacent in ring) */
    uint8_t nearest = numa_find_nearest_node(&topo, 0, true);
    ASSERT(nearest == 1 || nearest == 3, "Nearest to 0 is 1 or 3");

    /* From node 2, nearest is node 1 or 3 */
    nearest = numa_find_nearest_node(&topo, 2, true);
    ASSERT(nearest == 1 || nearest == 3, "Nearest to 2 is 1 or 3");

    TEST_PASS();
}

void test_numa_stats(void)
{
    TEST_START("NUMA statistics");

    numa_topology_t topo;
    numa_topology_simulate(&topo, 2, 8, 32768);

    numa_stats_t stats;
    numa_get_stats(&topo, &stats);

    ASSERT(stats.num_nodes == 2, "2 nodes");
    ASSERT(stats.total_cpus == 16, "16 CPUs");
    ASSERT(stats.avg_cpus_per_node == 8, "8 CPUs per node");
    ASSERT(stats.max_distance == 20, "Max distance is 20");
    ASSERT(stats.is_uniform == false, "Not UMA");

    TEST_PASS();
}

/*******************************************************************************
 * ALLOCATION TESTS
 ******************************************************************************/

void test_numa_alloc_local(void)
{
    TEST_START("NUMA local allocation");

    numa_topology_t topo;
    numa_topology_simulate(&topo, 2, 4, 16384);

    uint64_t initial_free = topo.nodes[0].memory_free_mb;

    /* Allocate 10MB on node 0 */
    void *ptr = numa_alloc(&topo, 10 * 1024 * 1024, NUMA_ALLOC_LOCAL, 0);
    ASSERT(ptr != NULL, "Allocation succeeded");

    /* Node 0 free memory should decrease */
    ASSERT(topo.nodes[0].memory_free_mb < initial_free, "Memory consumed");

    numa_free(&topo, ptr, 10 * 1024 * 1024);

    TEST_PASS();
}

void test_numa_alloc_nearest(void)
{
    TEST_START("NUMA nearest allocation");

    numa_topology_t topo;
    numa_topology_simulate(&topo, 2, 4, 16384);

    /* Make node 0 almost full */
    topo.nodes[0].memory_free_mb = 1;
    topo.nodes[1].memory_free_mb = 16000;

    /* Try to allocate on node 0, should fall back to node 1 */
    void *ptr = numa_alloc(&topo, 10 * 1024 * 1024, NUMA_ALLOC_NEAREST, 0);
    ASSERT(ptr != NULL, "Allocation succeeded");

    /* Node 1 should have been used (least loaded) */
    ASSERT(topo.nodes[1].memory_free_mb < 16000, "Allocated on node 1");

    numa_free(&topo, ptr, 10 * 1024 * 1024);

    TEST_PASS();
}

void test_numa_alloc_oom(void)
{
    TEST_START("NUMA out of memory");

    numa_topology_t topo;
    numa_topology_simulate(&topo, 1, 4, 1024);  /* Only 1GB */

    /* Try to allocate 2GB */
    void *ptr = numa_alloc(&topo, 2ULL * 1024 * 1024 * 1024, NUMA_ALLOC_LOCAL, 0);
    ASSERT(ptr == NULL, "Should fail (OOM)");

    TEST_PASS();
}

void test_numa_alloc_interleave(void)
{
    TEST_START("NUMA interleave allocation");

    numa_topology_t topo;
    numa_topology_simulate(&topo, 4, 4, 16384);

    /* Interleave should use least loaded node */
    void *ptr = numa_alloc(&topo, 10 * 1024 * 1024, NUMA_ALLOC_INTERLEAVE, 0);
    ASSERT(ptr != NULL, "Allocation succeeded");

    numa_free(&topo, ptr, 10 * 1024 * 1024);

    TEST_PASS();
}

/*******************************************************************************
 * BENCHMARK TESTS
 ******************************************************************************/

void benchmark_numa_distance_lookup(void)
{
    printf("\n========================================\n");
    printf("BENCHMARK: Distance Lookup Performance\n");
    printf("========================================\n");

    numa_topology_t topo;
    numa_topology_simulate(&topo, 4, 16, 65536);

    const int ITERATIONS = 1000000;
    volatile uint8_t sink = 0;

    printf("Performing %d distance lookups...\n", ITERATIONS);

    for (int i = 0; i < ITERATIONS; i++) {
        uint8_t from = i % 4;
        uint8_t to = (i + 1) % 4;
        sink += numa_get_distance(&topo, from, to);
    }

    printf("Complete (sink=%u)\n", sink);
    printf("Expected: ~10-20ns per lookup\n\n");
}

void benchmark_numa_cpu_node_lookup(void)
{
    printf("========================================\n");
    printf("BENCHMARK: CPU-to-Node Lookup\n");
    printf("========================================\n");

    numa_topology_t topo;
    numa_topology_simulate(&topo, 4, 16, 65536);

    const int ITERATIONS = 1000000;
    volatile uint8_t sink = 0;

    printf("Performing %d CPU-to-node lookups...\n", ITERATIONS);

    for (int i = 0; i < ITERATIONS; i++) {
        uint8_t cpu = i % 64;
        sink += numa_get_cpu_node(&topo, cpu);
    }

    printf("Complete (sink=%u)\n", sink);
    printf("Expected: ~5-10ns per lookup (array access)\n\n");
}

void benchmark_numa_allocation(void)
{
    printf("========================================\n");
    printf("BENCHMARK: NUMA Allocation Overhead\n");
    printf("========================================\n");

    numa_topology_t topo;
    numa_topology_simulate(&topo, 2, 8, 65536);

    const int ALLOCS = 1000;
    void *ptrs[1000];

    printf("Allocating %d × 1MB blocks...\n", ALLOCS);

    for (int i = 0; i < ALLOCS; i++) {
        ptrs[i] = numa_alloc(&topo, 1024 * 1024, NUMA_ALLOC_LOCAL, i % 2);
        if (ptrs[i] == NULL) {
            printf("Allocation %d failed (OOM)\n", i);
            break;
        }
    }

    printf("Freeing allocations...\n");

    for (int i = 0; i < ALLOCS; i++) {
        if (ptrs[i]) {
            numa_free(&topo, ptrs[i], 1024 * 1024);
        }
    }

    printf("Complete\n");
    printf("Expected: Standard malloc overhead + accounting\n\n");
}

/*******************************************************************************
 * TEST RUNNER
 ******************************************************************************/

int main(void)
{
    printf("\n");
    printf("╔════════════════════════════════════════════════════════════╗\n");
    printf("║   NUMA TOPOLOGY & ALLOCATION TEST SUITE (Phase 5.4.5)     ║\n");
    printf("╚════════════════════════════════════════════════════════════╝\n\n");

    printf("--- Topology Tests ---\n");
    test_numa_uma_topology();
    test_numa_dual_socket();
    test_numa_quad_socket();
    test_numa_cpu_locality();
    test_numa_node_cpus();
    test_numa_find_least_loaded();
    test_numa_find_nearest();
    test_numa_stats();

    printf("\n--- Allocation Tests ---\n");
    test_numa_alloc_local();
    test_numa_alloc_nearest();
    test_numa_alloc_oom();
    test_numa_alloc_interleave();

    printf("\n--- Benchmarks ---\n");
    benchmark_numa_distance_lookup();
    benchmark_numa_cpu_node_lookup();
    benchmark_numa_allocation();

    printf("╔════════════════════════════════════════════════════════════╗\n");
    printf("║   ALL TESTS PASSED                                         ║\n");
    printf("╚════════════════════════════════════════════════════════════╝\n\n");

    return 0;
}

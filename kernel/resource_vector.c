/**
 * @file resource_vector.c
 * @brief 8D Resource Vector Implementation (PDAC Framework)
 */

#include "types.h"
#include "defs.h"
#include "resource_vector.h"
#include "q16_fixed.h"
#include "q16_octonion.h"

/* ============================================================================
 * STRING CONVERSION AND DEBUGGING
 * ============================================================================ */

/**
 * Static buffer for string conversion (thread-unsafe, for debugging only)
 */
static char resource_str_buffer[256];

/**
 * Convert Q16.16 to integer with 2 decimal places
 */
static void q16_to_str(q16_t value, char *buf, int buf_size) {
    int integer_part = q16_to_int(value);
    int frac_part = ((value & 0xFFFF) * 100) >> 16;  /* Get 2 decimal places */

    /* Handle negative values */
    if (value < 0) {
        frac_part = -frac_part;
    }

    snprintf(buf, buf_size, "%d.%02d", integer_part, frac_part);
}

/**
 * Convert resource vector to human-readable string
 *
 * Format: "[CPU:100.00ms MEM:512.00MB IO:10.00MB/s NET:1000.00pps GPU:0.00 DISK:100.00iops IRQ:50.00/s CAPS:10.00]"
 */
const char* resource_vector_to_string(resource_vector_t v) {
    char cpu_str[32], mem_str[32], io_str[32], net_str[32];
    char gpu_str[32], disk_str[32], irq_str[32], caps_str[32];

    q16_to_str(v.e0, cpu_str, sizeof(cpu_str));
    q16_to_str(v.e1, mem_str, sizeof(mem_str));
    q16_to_str(v.e2, io_str, sizeof(io_str));
    q16_to_str(v.e3, net_str, sizeof(net_str));
    q16_to_str(v.e4, gpu_str, sizeof(gpu_str));
    q16_to_str(v.e5, disk_str, sizeof(disk_str));
    q16_to_str(v.e6, irq_str, sizeof(irq_str));
    q16_to_str(v.e7, caps_str, sizeof(caps_str));

    snprintf(resource_str_buffer, sizeof(resource_str_buffer),
             "[CPU:%sms MEM:%sMB IO:%sMB/s NET:%spps GPU:%s DISK:%siops IRQ:%s/s CAPS:%s]",
             cpu_str, mem_str, io_str, net_str, gpu_str, disk_str, irq_str, caps_str);

    return resource_str_buffer;
}

/**
 * Print resource vector to console (for debugging)
 */
void resource_vector_print(resource_vector_t v, const char *label) {
    if (label) {
        cprintf("%s: %s\n", label, resource_vector_to_string(v));
    } else {
        cprintf("%s\n", resource_vector_to_string(v));
    }
}

/* ============================================================================
 * PEDAGOGICAL EXAMPLES (compiled in debug mode)
 * ============================================================================ */

#ifdef DEBUG

/**
 * Example 1: Detect resource deadlock using zero divisors
 */
void example_deadlock_detection(void) {
    cprintf("\n=== Example 1: Deadlock Detection via Zero Divisors ===\n");

    /* Task A: CPU-intensive (high CPU, low everything else) */
    resource_vector_t task_a = RESOURCE_VEC(1000, 10, 0, 0, 0, 0, 0, 0);
    resource_vector_print(task_a, "Task A (CPU-intensive)");

    /* Task B: Memory-intensive (low CPU, high memory) */
    resource_vector_t task_b = RESOURCE_VEC(10, 4096, 0, 0, 0, 0, 0, 0);
    resource_vector_print(task_b, "Task B (Memory-intensive)");

    /* Compose tasks */
    resource_vector_t composition = resource_vector_compose(task_a, task_b);
    resource_vector_print(composition, "Composition (A * B)");

    /* Check for deadlock */
    if (resource_vector_is_orthogonal(task_a, task_b)) {
        cprintf("⚠️  WARNING: Tasks are orthogonal - potential DEADLOCK!\n");
        cprintf("   Explanation: Tasks require exclusive, non-overlapping resources.\n");
        cprintf("   If both acquire their resources, neither can proceed.\n");
    } else {
        cprintf("✓  Tasks can coexist (shared resource usage).\n");
    }

    cprintf("\n");
}

/**
 * Example 2: Non-associative path composition
 */
void example_path_dependence(void) {
    cprintf("\n=== Example 2: Non-Associative Path Composition ===\n");

    resource_vector_t task_a = RESOURCE_VEC(100, 512, 10, 100, 0, 10, 5, 1);
    resource_vector_t task_b = RESOURCE_VEC(200, 256, 20, 200, 0, 20, 10, 2);
    resource_vector_t task_c = RESOURCE_VEC(150, 384, 15, 150, 0, 15, 7, 1);

    resource_vector_print(task_a, "Task A");
    resource_vector_print(task_b, "Task B");
    resource_vector_print(task_c, "Task C");

    /* Path 1: (A → B) → C */
    resource_vector_t ab = resource_vector_compose(task_a, task_b);
    resource_vector_t path1 = resource_vector_compose(ab, task_c);
    resource_vector_print(path1, "Path 1: (A → B) → C");

    /* Path 2: A → (B → C) */
    resource_vector_t bc = resource_vector_compose(task_b, task_c);
    resource_vector_t path2 = resource_vector_compose(task_a, bc);
    resource_vector_print(path2, "Path 2: A → (B → C)");

    /* Compare norms (path-dependent!) */
    q16_t norm1 = resource_vector_norm(path1);
    q16_t norm2 = resource_vector_norm(path2);

    char norm1_str[32], norm2_str[32];
    q16_to_str(norm1, norm1_str, sizeof(norm1_str));
    q16_to_str(norm2, norm2_str, sizeof(norm2_str));

    cprintf("Path 1 norm: %s\n", norm1_str);
    cprintf("Path 2 norm: %s\n", norm2_str);

    if (norm1 != norm2) {
        cprintf("🔄 NON-ASSOCIATIVE: Execution order affects resource usage!\n");
        cprintf("   This is a feature, not a bug:\n");
        cprintf("   - DAG scheduling is inherently path-dependent\n");
        cprintf("   - Resource availability changes with execution order\n");
        cprintf("   - Octonion algebra models this naturally\n");
    } else {
        cprintf("✓  Paths are equivalent (rare case).\n");
    }

    cprintf("\n");
}

/**
 * Example 3: Resource quota management
 */
void example_quota_management(void) {
    cprintf("\n=== Example 3: Resource Quota Management ===\n");

    /* System quota (total available resources) */
    resource_vector_t system_quota = RESOURCE_VEC(10000, 16384, 1000, 100000, 0, 10000, 1000, 100);
    resource_vector_print(system_quota, "System Quota (Initial)");

    /* Task requirements */
    resource_vector_t web_server = RESOURCE_VEC_BALANCED;
    resource_vector_print(web_server, "Web Server Requirements");

    resource_vector_t database = RESOURCE_VEC(500, 8192, 500, 1000, 0, 5000, 100, 5);
    resource_vector_print(database, "Database Requirements");

    /* Try to allocate web server */
    if (resource_vector_allocate(&system_quota, web_server)) {
        cprintf("✓  Web server allocated successfully\n");
        resource_vector_print(system_quota, "System Quota (after web server)");
    } else {
        cprintf("❌ Web server allocation failed\n");
    }

    /* Try to allocate database */
    if (resource_vector_allocate(&system_quota, database)) {
        cprintf("✓  Database allocated successfully\n");
        resource_vector_print(system_quota, "System Quota (after database)");
    } else {
        cprintf("❌ Database allocation failed: insufficient resources\n");
    }

    /* Release web server resources */
    resource_vector_release(&system_quota, web_server);
    cprintf("✓  Web server resources released\n");
    resource_vector_print(system_quota, "System Quota (after release)");

    cprintf("\n");
}

/**
 * Run all PDAC pedagogical examples
 */
void pdac_run_examples(void) {
    cprintf("\n");
    cprintf("╔═══════════════════════════════════════════════════════════╗\n");
    cprintf("║  PDAC: Probabilistic DAG Algebra with Capabilities       ║\n");
    cprintf("║  Pedagogical Examples - 8D Resource Vectors              ║\n");
    cprintf("╚═══════════════════════════════════════════════════════════╝\n");

    example_deadlock_detection();
    example_path_dependence();
    example_quota_management();

    cprintf("╔═══════════════════════════════════════════════════════════╗\n");
    cprintf("║  Examples Complete                                        ║\n");
    cprintf("║  See PDAC_UNIFIED_FRAMEWORK.md for detailed explanation  ║\n");
    cprintf("╚═══════════════════════════════════════════════════════════╝\n");
    cprintf("\n");
}

#endif /* DEBUG */

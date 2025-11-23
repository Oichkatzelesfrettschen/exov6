/**
 * @file sched_test.c
 * @brief Preemptive Scheduler Verification Test (Phase 6b)
 *
 * This test proves that the OS can interrupt a non-cooperative thread.
 * If preemption is working, the "polite" thread will run even though
 * the "greedy" thread never yields.
 *
 * SUCCESS: "Polite: I am running!" appears
 * FAILURE: Hangs on "Greedy: I am starting..."
 */

#include <stdint.h>
#include <types.h>
#include <exov6_interface.h>

// Forward declarations
extern void print(const char *s);
extern void print_hex(uint64 n);
extern void scheduler_init(void);
extern int thread_create(void (*entry)(void*), void *arg, const char *name);
extern void thread_yield(void);
extern void libos_exception_init(void);

// Shared flag - set by polite worker, checked by greedy worker
volatile int flag = 0;

/**
 * Greedy Worker - Never yields, spins forever unless preempted
 *
 * In a cooperative-only scheduler, this would hang the OS.
 * With preemption, the timer interrupt will force a context switch.
 */
void greedy_worker(void *arg)
{
    (void)arg;
    print("Greedy: I am starting a busy loop.\n");
    print("Greedy: I will NEVER call yield()!\n");
    print("Greedy: If preemption fails, the OS dies here.\n");

    // Spin forever - NEVER YIELD
    // Without preemption, this loop runs until heat death of universe
    // With preemption, the timer will interrupt us
    while (flag == 0) {
        // Do nothing - just burn CPU
        // The timer interrupt must preempt us for any other thread to run
        __asm__ volatile("" ::: "memory");  // Prevent compiler from optimizing out
    }

    print("Greedy: I was broken out! Preemption works!\n");
}

/**
 * Polite Worker - Waits a bit, then sets the flag
 *
 * This thread should run because the timer preempts the greedy worker.
 */
void polite_worker(void *arg)
{
    (void)arg;
    print("Polite: I am running!\n");
    print("Polite: This proves preemption is working.\n");

    // Small delay (busy wait - but we'll be preempted anyway)
    for (volatile int i = 0; i < 100000; i++) {
        __asm__ volatile("" ::: "memory");
    }

    print("Polite: Setting flag to break greedy worker out.\n");
    flag = 1;

    print("Polite: Done. Exiting.\n");
}

int main(void)
{
    print("\n");
    print("═══════════════════════════════════════════════════════════\n");
    print("  SCHED_TEST: Preemptive Scheduler Verification\n");
    print("═══════════════════════════════════════════════════════════\n");
    print("\n");
    print("This test verifies that the OS can interrupt greedy threads.\n");
    print("If preemption is working:\n");
    print("  1. Greedy worker starts spinning\n");
    print("  2. Timer interrupt fires -> context switch\n");
    print("  3. Polite worker runs and sets flag\n");
    print("  4. Greedy worker sees flag and exits\n");
    print("\n");
    print("If preemption FAILS:\n");
    print("  - System hangs after 'Greedy: I am starting...'\n");
    print("\n");

    // Initialize exception handling (registers upcall handler with kernel)
    print("[1] Initializing exception handling...\n");
    libos_exception_init();

    // Initialize the scheduler
    print("[2] Initializing scheduler...\n");
    scheduler_init();

    // Create the greedy worker first (it will start spinning immediately)
    print("[3] Creating greedy worker (spins forever)...\n");
    int greedy_tid = thread_create(greedy_worker, 0, "greedy");
    if (greedy_tid < 0) {
        print("ERROR: Failed to create greedy worker!\n");
        return -1;
    }
    print("    Created thread ");
    print_hex(greedy_tid);
    print("\n");

    // Create the polite worker (will set flag to break greedy out)
    print("[4] Creating polite worker...\n");
    int polite_tid = thread_create(polite_worker, 0, "polite");
    if (polite_tid < 0) {
        print("ERROR: Failed to create polite worker!\n");
        return -1;
    }
    print("    Created thread ");
    print_hex(polite_tid);
    print("\n");

    // Main thread yields to let workers run
    print("[5] Main thread yielding to workers...\n");
    print("    (If you see this but nothing else, preemption failed)\n");
    print("\n");

    // Wait for flag to be set
    while (flag == 0) {
        thread_yield();
    }

    print("\n");
    print("═══════════════════════════════════════════════════════════\n");
    print("  TEST PASSED: Preemptive scheduling is working!\n");
    print("═══════════════════════════════════════════════════════════\n");
    print("\n");
    print("The OS successfully:\n");
    print("  1. Interrupted a non-cooperative (greedy) thread\n");
    print("  2. Switched context via timer interrupt upcall\n");
    print("  3. Allowed another thread to run\n");
    print("\n");
    print("This proves the 'Heartbeat' of the OS is alive.\n");
    print("\n");

    // Don't actually exit - spin forever for QEMU
    while (1) {
#if defined(__x86_64__)
        __asm__ volatile("hlt");
#elif defined(__aarch64__)
        __asm__ volatile("wfi");  // Wait For Interrupt (ARM64)
#else
        __asm__ volatile("" ::: "memory");  // Generic busy-wait
#endif
    }

    return 0;
}

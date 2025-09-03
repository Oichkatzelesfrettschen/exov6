#include "include/quaternion_spinlock.h"
#include "include/octonion.h" // For quaternion_create, etc.
#include <stdio.h> // For printf
#include <string.h> // For strcmp

#include "include/defs.h" // Expected to provide mycpu() via proc.h or similar
#include "engine/kernel/spinlock.h" // Expected to declare getcallerpcs()
// Potentially include "kernel/proc.h" if mycpu() or struct cpu isn't fully available via defs.h
// struct cpu is forward declared in quaternion_spinlock.h, full def needed if fields accessed.
// For this test, we might only need its pointer for mycpu() comparison.

// The mock_cpus array and current_mock_cpu_id are kept to associate the cpu_id parameter
// of qspin_lock with a conceptual CPU index for the test logic.
// The actual mycpu() will be called by qspin_lock internally.
static int current_mock_cpu_id = 0; // Represents the CPU ID passed to qspin_lock
struct cpu mock_cpus[2]; // Array of struct cpu for conceptual assignment, not for mycpu() mock

// Helper for printing test results
void test_assert(int condition, const char* test_name) {
    if (condition) {
        printf("[PASS] %s\n", test_name);
    } else {
        printf("[FAIL] %s\n", test_name);
    }
}

int main(void) {
    qspin_lock_t test_lock;
    const char* lock_name = "test_lock_1";

    printf("--- Running Quaternion Spinlock Tests ---\n");

    // Test 1: Initialization
    qspin_lock_init(&test_lock, lock_name);
    test_assert(test_lock.locked_flag == 0, "Test 1.1: Init - locked_flag is 0");
    test_assert(test_lock.name == lock_name, "Test 1.2: Init - name is set");
    test_assert(test_lock.cpu == 0, "Test 1.3: Init - cpu is NULL");
    // Assuming QSPIN_NO_OWNER_POS is {0,0,0,0} for comparison
    quaternion_t no_owner = {0,0,0,0};
    test_assert(memcmp(&test_lock.current_owner_pos, &no_owner, sizeof(quaternion_t)) == 0, "Test 1.4: Init - current_owner_pos is zeroed");


    // Test 2: Basic Lock and Unlock
    current_mock_cpu_id = 0; // CPU 0 acquires the lock
    printf("Attempting lock by CPU 0...\n");
    qspin_lock(&test_lock, current_mock_cpu_id);
    printf("Lock acquired by CPU 0.\n");
    test_assert(test_lock.locked_flag == 1, "Test 2.1: Lock - locked_flag is 1");
    // test_lock.cpu should be the actual current CPU returned by the real mycpu()
    test_assert(test_lock.cpu == mycpu(), "Test 2.2: Lock - cpu is mycpu()");
    test_assert(qspin_holding(&test_lock), "Test 2.3: Lock - qspin_holding is true for current CPU owner");

    // Test 2.4: Check current_owner_pos (simplified check of w component)
    quaternion_t expected_pos_cpu0 = quaternion_from_cpu_id(current_mock_cpu_id); // cpu_id passed to qspin_lock
    test_assert(test_lock.current_owner_pos.w == expected_pos_cpu0.w, "Test 2.4: Lock - current_owner_pos.w matches locking cpu_id");

    // Test 2.5: Holding by another CPU (conceptual)
    // If mycpu() is truly the current CPU, and it holds the lock, then qspin_holding(&test_lock) is true.
    // To test if another CPU *would not* be holding it, we'd need to run code as another CPU.
    // In a single-threaded test, we can only verify that if the lock is held, qspin_holding is true,
    // and if we unlock it, qspin_holding becomes false.
    // The old test `current_mock_cpu_id = 1; test_assert(!qspin_holding(&test_lock));`
    // implicitly tested the mock mycpu(). Now, it will test if the *actual* current CPU (still CPU 0 context)
    // is *not* CPU 1 (which is true, but not the original intent).
    // A more meaningful test for "holding by another CPU" would be:
    // 1. CPU A locks. qspin_holding() by CPU A is true.
    // 2. CPU B tries to lock (and spins or fails if trylock). qspin_holding() by CPU B is false.
    // This requires multi-threading or a more sophisticated test harness.
    // For now, we accept that this specific test case (2.5) changes meaning.
    // If the lock is held by current CPU (0), and we conceptually check for CPU 1, it should be false.
    // This is effectively what qspin_holding does: `lock->cpu == mycpu()`. If mycpu() is fixed,
    // then this test is just `lock->cpu == fixed_mycpu_val`.
    // The previous test was: `mock_cpus[current_mock_cpu_id_for_lock] == mock_cpus[current_mock_cpu_id_for_holding_check]`
    // Let's assume for Test 2.5, the lock is held by CPU 0.
    // If mycpu() returns context for CPU 0, then `!qspin_holding(&test_lock)` would be false.
    // This test needs to be re-thought or removed if we cannot mock mycpu() behavior for the check.
    // For now, let's verify that if current CPU holds it, qspin_holding is true, and after unlock, it's false.
    // The specific check "qspin_holding is false for other CPU" is hard to do now without context switching.
    // We can, however, check that if the lock *is* held, calling qspin_holding from a different CPU context
    // (if that were possible to simulate) would yield false.
    // The old test case logic:
    // current_mock_cpu_id = 1; // Simulate checking from CPU 1's perspective
    // test_assert(!qspin_holding(&test_lock), "Test 2.5: Lock - qspin_holding is false for other CPU (conceptual)");
    // current_mock_cpu_id = 0; // Switch back
    // This test (2.5) is removed for now as it relied on mocking mycpu().
    // A new test could be: ensure a different CPU *cannot* unlock it (implicitly tested by not panicking).

    printf("Attempting unlock by CPU 0 (current CPU)...\n");
    qspin_unlock(&test_lock);
    printf("Lock unlocked by CPU 0.\n");
    test_assert(test_lock.locked_flag == 0, "Test 2.6: Unlock - locked_flag is 0");
    test_assert(test_lock.cpu == 0, "Test 2.7: Unlock - cpu is NULL");
    test_assert(memcmp(&test_lock.current_owner_pos, &no_owner, sizeof(quaternion_t)) == 0, "Test 2.8: Unlock - current_owner_pos is zeroed");
    test_assert(!qspin_holding(&test_lock), "Test 2.9: Unlock - qspin_holding is false after unlock");

    // Test 3: Sequential Lock/Unlock (Relock)
    current_mock_cpu_id = 1; // CPU 1 acquires the lock
    printf("Attempting lock by CPU 1...\n");
    qspin_lock(&test_lock, current_mock_cpu_id);
    printf("Lock acquired by CPU 1.\n");
    test_assert(test_lock.locked_flag == 1, "Test 3.1: Relock - locked_flag is 1");
    // test_lock.cpu should be the actual current CPU returned by the real mycpu()
    test_assert(test_lock.cpu == mycpu(), "Test 3.2: Relock - cpu is mycpu()");
    quaternion_t expected_pos_cpu1 = quaternion_from_cpu_id(current_mock_cpu_id); // cpu_id passed to qspin_lock
    test_assert(test_lock.current_owner_pos.w == expected_pos_cpu1.w, "Test 3.3: Relock - current_owner_pos.w matches locking cpu_id (CPU 1)");

    printf("Attempting unlock by CPU 1 (current CPU)...\n");
    qspin_unlock(&test_lock);
    printf("Lock unlocked by CPU 1 (current CPU).\n");
    test_assert(test_lock.locked_flag == 0, "Test 3.4: Relock - locked_flag is 0");


    // Test 4: Trylock (Placeholder - qspin_trylock is not implemented yet)
    // printf("Test 4: Trylock - SKIPPED (qspin_trylock not implemented)\n");
    // qspin_lock_t trylock_test;
    // qspin_lock_init(&trylock_test, "trylock_test");
    // current_mock_cpu_id = 0;
    // if (qspin_trylock(&trylock_test, current_mock_cpu_id)) {
    //    test_assert(trylock_test.locked_flag == 1, "Test 4.1: Trylock success - locked_flag is 1");
    //    qspin_unlock(&trylock_test);
    // } else {
    //    test_assert(0, "Test 4.1: Trylock failed (unexpected for first try)");
    // }
    // current_mock_cpu_id = 1;
    // qspin_lock(&trylock_test, current_mock_cpu_id); // Lock it with CPU 1
    // current_mock_cpu_id = 0;
    // test_assert(!qspin_trylock(&trylock_test, current_mock_cpu_id), "Test 4.2: Trylock should fail when held by another");
    // qspin_unlock(&trylock_test); // Release by CPU 1

    printf("--- Quaternion Spinlock Tests Complete ---\n");
    return 0;
}

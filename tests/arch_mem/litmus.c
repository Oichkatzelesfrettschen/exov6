/*
 * litmus.c - Memory Ordering Litmus Tests
 */

#include <hal/arch_ops.h>
#include <stdio.h>
#include <pthread.h>
#include <stdatomic.h>
#include <assert.h>
#include <unistd.h>

// Configuration
#define ITERATIONS 100000

// ---------------------------------------------------------------------------
// Message Passing (MP) Litmus Test
// ---------------------------------------------------------------------------
// Thread 0: data = 1; arch_barrier_write(); flag = 1;
// Thread 1: if (flag == 1) { arch_barrier_read(); assert(data == 1); }

int mp_data = 0;
int mp_flag = 0;

void* mp_thread0(void* arg) {
    (void)arg;
    for (int i = 0; i < ITERATIONS; i++) {
        mp_data = 1;
        arch_barrier_write(); // sfence
        __atomic_store_n(&mp_flag, 1, __ATOMIC_RELAXED);

        // Reset for next iter (sync needed)
        while (__atomic_load_n(&mp_flag, __ATOMIC_RELAXED) != 0) {
             // spin
             arch_cpu_relax();
        }
    }
    return NULL;
}

void* mp_thread1(void* arg) {
    (void)arg;
    for (int i = 0; i < ITERATIONS; i++) {
        while (__atomic_load_n(&mp_flag, __ATOMIC_RELAXED) == 0) {
            arch_cpu_relax();
        }

        arch_barrier_read(); // lfence
        int d = mp_data;

        if (d != 1) {
            printf("MP Violation detected at iter %d! data=%d\n", i, d);
        }

        __atomic_store_n(&mp_flag, 0, __ATOMIC_RELAXED);
    }
    return NULL;
}

// ---------------------------------------------------------------------------
// Dekker's Algorithm (Mutual Exclusion check)
// ---------------------------------------------------------------------------
// flag0 = 1; barrier; if (flag1 == 0) enter_critical;
// flag1 = 1; barrier; if (flag0 == 0) enter_critical;
// Check: at most one thread in critical section.

int dekker_flag0 = 0;
int dekker_flag1 = 0;
int critical_count = 0;
int violations = 0;

void* dekker_thread0(void* arg) {
    (void)arg;
    for (int i = 0; i < ITERATIONS; i++) {
        __atomic_store_n(&dekker_flag0, 1, __ATOMIC_RELAXED);
        arch_barrier_full(); // mfence

        if (__atomic_load_n(&dekker_flag1, __ATOMIC_RELAXED) == 0) {
            // Critical section
            __atomic_fetch_add(&critical_count, 1, __ATOMIC_RELAXED);

            if (critical_count > 1) {
                 __atomic_fetch_add(&violations, 1, __ATOMIC_RELAXED);
            }

            __atomic_fetch_sub(&critical_count, 1, __ATOMIC_RELAXED);
        }

        __atomic_store_n(&dekker_flag0, 0, __ATOMIC_RELAXED);
    }
    return NULL;
}

void* dekker_thread1(void* arg) {
    (void)arg;
    for (int i = 0; i < ITERATIONS; i++) {
        __atomic_store_n(&dekker_flag1, 1, __ATOMIC_RELAXED);
        arch_barrier_full(); // mfence

        if (__atomic_load_n(&dekker_flag0, __ATOMIC_RELAXED) == 0) {
            // Critical section
            __atomic_fetch_add(&critical_count, 1, __ATOMIC_RELAXED);

            if (critical_count > 1) {
                 __atomic_fetch_add(&violations, 1, __ATOMIC_RELAXED);
            }

            __atomic_fetch_sub(&critical_count, 1, __ATOMIC_RELAXED);
        }

        __atomic_store_n(&dekker_flag1, 0, __ATOMIC_RELAXED);
    }
    return NULL;
}


int main() {
    pthread_t t1, t2;

    printf("Running MP test (%d iterations)...\n", ITERATIONS);
    pthread_create(&t1, NULL, mp_thread0, NULL);
    pthread_create(&t2, NULL, mp_thread1, NULL);
    pthread_join(t1, NULL);
    pthread_join(t2, NULL);

    // Reset all global variables between tests
    mp_data = 0;
    mp_flag = 0;
    dekker_flag0 = 0;
    dekker_flag1 = 0;
    critical_count = 0;
    violations = 0;

    printf("Running Dekker test (%d iterations)...\n", ITERATIONS);
    pthread_create(&t1, NULL, dekker_thread0, NULL);
    pthread_create(&t2, NULL, dekker_thread1, NULL);
    pthread_join(t1, NULL);
    pthread_join(t2, NULL);

    if (violations > 0) {
        printf("Dekker Violations detected: %d\n", violations);
        return 1;
    }

    printf("Tests complete. No violations.\n");
    return 0;
}

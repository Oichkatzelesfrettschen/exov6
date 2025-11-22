/**
 * @file test_ipc_torture.c
 * @brief Stress test for Lock-Free IPC (FastIPC)
 *
 * Simulates multi-threaded IPC communication to verify
 * memory ordering, data integrity, and performance.
 *
 * MODELED AFTER: Linux rcutorture
 */

#define _GNU_SOURCE
#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <errno.h>
#include <assert.h>
#include <unistd.h>
#include <stdatomic.h>

/* Setup environment to include kernel source */
/* We mock HAL and other dependencies */

#include "hal/hal.h"

/* Mock HAL globals */
const hal_t *hal_current = NULL;

/* Mock HAL implementations */
static void mock_cpu_pause(void) {
    /* Pause to allow other threads to run (simulating spin loop) */
    sched_yield();
}

static uint64_t mock_read_timestamp(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (uint64_t)ts.tv_sec * 1000000000ULL + ts.tv_nsec;
}

static hal_cpu_ops_t mock_cpu_ops = {
    .cpu_pause = mock_cpu_pause,
    .read_timestamp = mock_read_timestamp
};

static hal_t mock_hal = {
    .cpu = &mock_cpu_ops
};

/* Include the IPC implementation directly to access internal state */
/* We need to define some types that might be missing if we don't link full kernel */
#include "ipc/unified_ipc.c"

/* Test Configuration */
#define TEST_DURATION_SEC 5
#define NUM_SENDERS 4
#define NUM_ITERATIONS 100000

/* Global Test State */
static atomic_bool test_running = true;
static uint64_t receiver_endpoint;
static atomic_ulong total_messages = 0;
static atomic_ulong total_errors = 0;

/* Receiver Thread */
void *receiver_thread(void *arg) {
    (void)arg;
    uint64_t regs[8];

    printf("Receiver started on endpoint %lu\n", receiver_endpoint);

    while (atomic_load(&test_running)) {
        /* Poll for message */
        int ret = fastipc_recv(ipc_endpoint_lookup(receiver_endpoint), regs);

        if (ret == 0) {
            /* Process message: echo back with modification */
            /* Verify integrity: regs[0] should contain sender ID */
            /* We multiply regs[1] by 2 as the result */

            regs[0] = regs[0]; /* Preserve sender ID */
            regs[1] = regs[1] * 2;

            /* Reply */
            ret = fastipc_reply(receiver_endpoint, regs);
            if (ret != 0) {
                fprintf(stderr, "Receiver reply failed: %d\n", ret);
                atomic_fetch_add(&total_errors, 1);
            }

            atomic_fetch_add(&total_messages, 1);
        } else if (ret != -ETIMEDOUT) {
            /* Ignore timeouts (just polling), report other errors */
            fprintf(stderr, "Receiver recv failed: %d\n", ret);
            atomic_fetch_add(&total_errors, 1);
        }
    }

    return NULL;
}

/* Sender Thread */
void *sender_thread(void *arg) {
    long id = (long)arg;
    uint64_t regs[8];
    uint64_t result[8];

    /* Allocate sender endpoint (not strictly used by fastipc_call but good for context) */
    ipc_endpoint_t *ep = ipc_endpoint_alloc(IPC_TYPE_FASTIPC);
    uint64_t sender_ep_id = atomic_load(&ep->data.id);

    printf("Sender %ld started (ep %lu)\n", id, sender_ep_id);

    /* We reuse the same endpoint for calls? No, fastipc_call takes DESTINATION endpoint ID.
       The source endpoint is implicit in the thread context in real kernel,
       but here fastipc_call uses the destination endpoint struct to coordinate.

       Wait, FastIPC is Synchronous. The destination endpoint has the 'ready' flag.
       Multiple senders competing for the same destination endpoint?

       If multiple senders call fastipc_call(dest, ...), they will race on 'ready' flag.
       fastipc_call does:
       atomic_store(&ready, 1, release);

       If two senders do this, one overwrites the other!
       FastIPC is usually 1-to-1 or needs a lock on the caller side if shared?
       Or does the endpoint belong to the RECEIVER (server)? Yes.
       So multiple clients calling the same server.

       If multiple clients write to the same 'ready' flag, it is a RACE.
       L4 IPC usually handles this by queuing senders or refusing if busy.

       Current implementation of fastipc_call:
         atomic_store(&ready, 1)
       This stomps.

       We need CAS(ready, 0, 1) to acquire the channel!

       Ah! Verify if unified_ipc.c handles contention.

       In fastipc_call:
       atomic_store_explicit(&ep->data.proto.fastipc.ready, 1, memory_order_release);

       It does NOT use CAS. So it assumes single sender or external synchronization?
       OR, this IS a bug/limitation I need to expose.

       "Risks: ... blocked receiver"

       If I run multiple senders, I expect failures or corruption if not handled.
       The doc I wrote says: "Contention: Multiple senders targeting same receiver (should be serialized or fail gracefully)."

       Let's test CAS fix requirement.
    */

    uint64_t counter = 0;
    while (atomic_load(&test_running) && counter < NUM_ITERATIONS) {
        regs[0] = id;       /* Sender ID */
        regs[1] = counter;  /* Sequence */

        /* Attempt call */
        int ret = fastipc_call(receiver_endpoint, regs, result);

        if (ret == 0) {
            /* Verify result */
            if (result[0] != (uint64_t)id) {
                fprintf(stderr, "Sender %ld: ID mismatch in reply (got %lu)\n", id, result[0]);
                atomic_fetch_add(&total_errors, 1);
            }
            if (result[1] != counter * 2) {
                fprintf(stderr, "Sender %ld: Value mismatch (sent %lu, got %lu)\n", id, counter, result[1]);
                atomic_fetch_add(&total_errors, 1);
            }
            counter++;
        } else if (ret == -ETIMEDOUT) {
            /* Timeout is acceptable under load */
        } else {
            fprintf(stderr, "Sender %ld: Call failed: %d\n", id, ret);
            atomic_fetch_add(&total_errors, 1);
        }

        /* Random yield to increase race probability */
        if (rand() % 100 == 0) sched_yield();
    }

    return NULL;
}

int main(void) {
    printf("=== IPC Torture Test ===\n");

    /* Init HAL */
    hal_current = &mock_hal;

    /* Init IPC */
    ipc_init();

    /* Create Receiver Endpoint */
    ipc_endpoint_t *rx_ep = ipc_endpoint_alloc(IPC_TYPE_FASTIPC);
    receiver_endpoint = atomic_load(&rx_ep->data.id);

    /* Set valid capability for testing (check is stubbed to always return 1 in unified_ipc.c for now) */
    rx_ep->data.cap_id = 100;

    printf("Created receiver endpoint %lu\n", receiver_endpoint);

    /* Create Threads */
    pthread_t rx_thread;
    pthread_t tx_threads[NUM_SENDERS];

    pthread_create(&rx_thread, NULL, receiver_thread, NULL);

    for (long i = 0; i < NUM_SENDERS; i++) {
        pthread_create(&tx_threads[i], NULL, sender_thread, (void*)i);
    }

    /* Run Test */
    sleep(TEST_DURATION_SEC);

    /* Stop */
    atomic_store(&test_running, false);

    pthread_join(rx_thread, NULL);
    for (int i = 0; i < NUM_SENDERS; i++) {
        pthread_join(tx_threads[i], NULL);
    }

    printf("\n=== Test Results ===\n");
    printf("Total Messages: %lu\n", atomic_load(&total_messages));
    printf("Total Errors:   %lu\n", atomic_load(&total_errors));

    if (atomic_load(&total_errors) > 0) {
        printf("FAIL: Errors detected\n");
        return 1;
    }

    /* Performance Check */
    double rate = (double)atomic_load(&total_messages) / TEST_DURATION_SEC;
    printf("Rate: %.0f msgs/sec\n", rate);

    if (rate < 1000) {
        printf("WARN: Performance seems low (expected >1k/sec)\n");
    }

    printf("PASS\n");
    return 0;
}

/**
 * @file lockfree.c
 * @brief Lock-Free Data Structures Implementation
 *
 * IMPLEMENTATION NOTES:
 * =====================
 * This file implements state-of-the-art lock-free algorithms:
 *
 * 1. **Hazard Pointers** (Maged Michael, 2004)
 *    - Safe memory reclamation without garbage collection
 *    - Threads "protect" pointers they're using
 *    - Retired nodes scanned periodically to free unreferenced memory
 *
 * 2. **Michael-Scott Queue** (Maged Michael & Michael Scott, 1996)
 *    - MPMC (Multi-Producer Multi-Consumer) FIFO queue
 *    - Lock-free: at least one thread always makes progress
 *    - Used in Java's ConcurrentLinkedQueue
 *
 * 3. **Treiber Stack** (R. Kent Treiber, 1986)
 *    - Lock-free LIFO stack
 *    - Simple CAS-based algorithm
 *    - Used in many lock-free memory allocators
 *
 * LINEARIZATION POINTS:
 * =====================
 * Each operation has a linearization point where it "takes effect":
 * - enqueue: CAS that swings tail->next
 * - dequeue: CAS that advances head
 * - push: CAS that updates top
 * - pop: CAS that advances top
 *
 * MEMORY ORDERING:
 * ================
 * We use explicit memory ordering for performance:
 * - acquire: Load with synchronization (read barrier)
 * - release: Store with synchronization (write barrier)
 * - acq_rel: Both acquire and release
 * - seq_cst: Sequentially consistent (strongest, default)
 * - relaxed: No synchronization (statistics only)
 */

#include "lockfree.h"
#include <stdlib.h>
#include <string.h>
#include <pthread.h>
#include <stdio.h>

/*******************************************************************************
 * THREAD-LOCAL STORAGE
 ******************************************************************************/

/**
 * Thread-local thread ID (for single-threaded simulation)
 */
__thread int simulated_tid = 0;

/**
 * Get current thread ID
 *
 * In a real implementation, this would use pthread_self() and a hash table.
 * For pedagogical purposes, we use simulated TIDs.
 */
int get_thread_id(void) {
    return simulated_tid;
}

/*******************************************************************************
 * HAZARD POINTERS - Memory Reclamation
 ******************************************************************************/

/**
 * Initialize hazard pointer domain
 *
 * Sets all hazard pointers to NULL and inactive.
 */
void hp_domain_init(hp_domain_t *domain) {
    /* Initialize all hazard pointers */
    for (int i = 0; i < HP_MAX_THREADS * HP_PER_THREAD; i++) {
        atomic_store(&domain->hps[i].ptr, NULL);
        atomic_store(&domain->hps[i].active, 0);
    }

    /* Initialize retired lists */
    for (int i = 0; i < HP_MAX_THREADS; i++) {
        domain->retire_lists[i] = NULL;
        atomic_store(&domain->retire_counts[i], 0);
    }
}

/**
 * Acquire a hazard pointer for use
 *
 * Finds the first inactive HP for this thread and marks it active.
 *
 * @param domain  HP domain
 * @param tid     Thread ID
 * @param hp_idx  Hazard pointer index (0 to HP_PER_THREAD-1)
 * @return        Pointer to HP record
 */
hazard_pointer_t *hp_acquire(hp_domain_t *domain, int tid, int hp_idx) {
    int hp_global_idx = tid * HP_PER_THREAD + hp_idx;
    hazard_pointer_t *hp = &domain->hps[hp_global_idx];

    /* Mark as active */
    atomic_store(&hp->active, 1);

    return hp;
}

/**
 * Protect a pointer with hazard pointer (with retry loop)
 *
 * ALGORITHM:
 * 1. Load source pointer
 * 2. Store in hazard pointer
 * 3. Re-load source to verify it hasn't changed
 * 4. If changed, retry (prevents use-after-free)
 *
 * This is the "standard" hazard pointer protection pattern.
 *
 * @param hp   Hazard pointer to use
 * @param src  Atomic pointer to protect
 * @return     Protected value (may be NULL if retry failed)
 */
void *hp_protect(hazard_pointer_t *hp, atomic_ptr_t *src) {
    void *p;
    void *q;

    do {
        /* Load pointer we want to protect */
        p = atomic_load_explicit(src, memory_order_acquire);

        /* Store in hazard pointer (announce we're using it) */
        atomic_store_explicit(&hp->ptr, p, memory_order_release);

        /* Verify it hasn't changed (prevents ABA-like races) */
        q = atomic_load_explicit(src, memory_order_acquire);
    } while (p != q);

    return p;
}

/**
 * Clear hazard pointer (stop protecting)
 *
 * @param hp  Hazard pointer to clear
 */
void hp_clear(hazard_pointer_t *hp) {
    atomic_store_explicit(&hp->ptr, NULL, memory_order_release);
    atomic_store(&hp->active, 0);
}

/**
 * Retire a node for later deletion
 *
 * Adds node to per-thread retire list. When list reaches threshold,
 * triggers scan to free unreferenced nodes.
 *
 * @param domain   HP domain
 * @param tid      Thread ID
 * @param ptr      Pointer to retire
 * @param deleter  Deletion function
 */
void hp_retire(hp_domain_t *domain, int tid, void *ptr, void (*deleter)(void*)) {
    /* Create retired node */
    retired_node_t *node = (retired_node_t*)malloc(sizeof(retired_node_t));
    node->ptr = ptr;
    node->deleter = deleter;

    /* Add to retire list (lock-free single-producer prepend) */
    node->next = domain->retire_lists[tid];
    domain->retire_lists[tid] = node;

    /* Increment count */
    int count = atomic_fetch_add(&domain->retire_counts[tid], 1) + 1;

    /* Trigger scan if threshold reached */
    if (count >= HP_RETIRE_THRESHOLD) {
        hp_scan(domain, tid);
    }
}

/**
 * Scan retired list and free unreferenced nodes
 *
 * ALGORITHM:
 * 1. Collect all active hazard pointers into set H
 * 2. For each retired node:
 *    - If ptr ∈ H: keep in retire list (still referenced)
 *    - If ptr ∉ H: free it (no references)
 *
 * This is the key reclamation mechanism: we can only free when
 * no hazard pointer is protecting the memory.
 *
 * @param domain  HP domain
 * @param tid     Thread ID
 */
void hp_scan(hp_domain_t *domain, int tid) {
    /* Step 1: Collect all active hazard pointers */
    void *hazards[HP_MAX_THREADS * HP_PER_THREAD];
    int num_hazards = 0;

    for (int i = 0; i < HP_MAX_THREADS * HP_PER_THREAD; i++) {
        if (atomic_load(&domain->hps[i].active)) {
            void *p = atomic_load_explicit(&domain->hps[i].ptr,
                                           memory_order_acquire);
            if (p != NULL) {
                hazards[num_hazards++] = p;
            }
        }
    }

    /* Step 2: Scan retire list */
    retired_node_t *curr = domain->retire_lists[tid];
    retired_node_t *new_list = NULL;
    int new_count = 0;

    while (curr != NULL) {
        retired_node_t *next = curr->next;

        /* Check if pointer is in hazard set */
        bool is_hazard = false;
        for (int i = 0; i < num_hazards; i++) {
            if (hazards[i] == curr->ptr) {
                is_hazard = true;
                break;
            }
        }

        if (is_hazard) {
            /* Keep in retire list (still referenced) */
            curr->next = new_list;
            new_list = curr;
            new_count++;
        } else {
            /* Free it (no references) */
            if (curr->deleter) {
                curr->deleter(curr->ptr);
            } else {
                free(curr->ptr);
            }
            free(curr);
        }

        curr = next;
    }

    /* Update retire list */
    domain->retire_lists[tid] = new_list;
    atomic_store(&domain->retire_counts[tid], new_count);
}

/*******************************************************************************
 * MICHAEL-SCOTT LOCK-FREE QUEUE (MPMC)
 ******************************************************************************/

/**
 * Initialize Michael-Scott queue
 *
 * Creates sentinel node (dummy node) to simplify edge cases.
 * Both head and tail initially point to sentinel.
 *
 * @param queue  Queue to initialize
 * @param hp     Hazard pointer domain
 */
void ms_queue_init(ms_queue_t *queue, hp_domain_t *hp) {
    /* Create sentinel node */
    ms_node_t *sentinel = (ms_node_t*)malloc(sizeof(ms_node_t));
    sentinel->data = NULL;
    atomic_store(&sentinel->next, NULL);

    /* Both head and tail point to sentinel */
    atomic_store(&queue->head, sentinel);
    atomic_store(&queue->tail, sentinel);

    queue->hp = hp;

    /* Initialize statistics */
    atomic_store(&queue->enqueue_count, 0);
    atomic_store(&queue->dequeue_count, 0);
}

/**
 * Enqueue data (lock-free)
 *
 * ALGORITHM (Michael & Scott, 1996):
 * 1. Allocate new node with data
 * 2. Loop:
 *    a. Read tail pointer
 *    b. Read tail->next
 *    c. If tail->next is NULL:
 *       - Try CAS(tail->next, NULL, node)
 *       - If success: try to swing tail forward (linearization point)
 *    d. Else: help other thread by swinging tail
 *
 * LINEARIZATION POINT: CAS that sets tail->next
 *
 * @param queue  Queue
 * @param data   Data to enqueue
 * @param tid    Thread ID
 */
void ms_enqueue(ms_queue_t *queue, void *data, int tid) {
    /* Allocate new node */
    ms_node_t *node = (ms_node_t*)malloc(sizeof(ms_node_t));
    node->data = data;
    atomic_store(&node->next, NULL);

    /* Get hazard pointers */
    hazard_pointer_t *hp_tail = hp_acquire(queue->hp, tid, 0);

    while (true) {
        /* Read tail */
        ms_node_t *tail = hp_protect(hp_tail, &queue->tail);
        if (tail == NULL) continue;  /* Retry if protection failed */

        /* Read next */
        ms_node_t *next = atomic_load_explicit(&tail->next, memory_order_acquire);

        /* Verify tail is still consistent */
        ms_node_t *tail_verify = atomic_load(&queue->tail);
        if (tail != tail_verify) {
            continue;  /* Tail changed, retry */
        }

        if (next == NULL) {
            /* Tail is indeed last node, try to link new node */
            /* LINEARIZATION POINT: This CAS makes enqueue "happen" */
            if (atomic_compare_exchange_weak_explicit(
                    &tail->next, &next, node,
                    memory_order_release,  /* success: publish node */
                    memory_order_acquire)) /* failure: re-read next */
            {
                /* Success! Try to swing tail forward (best effort) */
                atomic_compare_exchange_weak(&queue->tail, &tail, node);

                /* Update statistics */
                atomic_fetch_add_explicit(&queue->enqueue_count, 1,
                                          memory_order_relaxed);

                hp_clear(hp_tail);
                return;
            }
        } else {
            /* Tail is not last node, help advance it */
            atomic_compare_exchange_weak(&queue->tail, &tail, next);
        }
    }
}

/**
 * Dequeue data (lock-free)
 *
 * ALGORITHM (Michael & Scott, 1996):
 * 1. Loop:
 *    a. Read head, tail, head->next
 *    b. If queue appears empty (head == tail && next == NULL):
 *       - Return NULL
 *    c. If head == tail but next != NULL:
 *       - Tail is behind, help advance it
 *    d. Else:
 *       - Try CAS(head, old_head, next) (linearization point)
 *       - If success: retire old head, return data
 *
 * LINEARIZATION POINT: CAS that advances head
 *
 * @param queue  Queue
 * @param tid    Thread ID
 * @return       Dequeued data, or NULL if empty
 */
void *ms_dequeue(ms_queue_t *queue, int tid) {
    /* Get hazard pointers */
    hazard_pointer_t *hp_head = hp_acquire(queue->hp, tid, 0);
    hazard_pointer_t *hp_next = hp_acquire(queue->hp, tid, 1);

    while (true) {
        /* Read head */
        ms_node_t *head = hp_protect(hp_head, &queue->head);
        if (head == NULL) continue;

        /* Read tail */
        ms_node_t *tail = atomic_load(&queue->tail);

        /* Read head->next */
        ms_node_t *next = hp_protect(hp_next, &head->next);

        /* Verify head is still consistent */
        ms_node_t *head_verify = atomic_load(&queue->head);
        if (head != head_verify) {
            continue;  /* Head changed, retry */
        }

        if (head == tail) {
            if (next == NULL) {
                /* Queue is empty */
                hp_clear(hp_head);
                hp_clear(hp_next);
                return NULL;
            }

            /* Tail is behind, help advance it */
            atomic_compare_exchange_weak(&queue->tail, &tail, next);
        } else {
            /* Queue is not empty */
            if (next == NULL) {
                continue;  /* Inconsistent state, retry */
            }

            /* Read data BEFORE CAS (critical!) */
            void *data = next->data;

            /* LINEARIZATION POINT: This CAS makes dequeue "happen" */
            if (atomic_compare_exchange_weak_explicit(
                    &queue->head, &head, next,
                    memory_order_release,  /* success: publish new head */
                    memory_order_acquire)) /* failure: re-read head */
            {
                /* Success! Retire old head using hazard pointers */
                hp_retire(queue->hp, tid, head, free);

                /* Update statistics */
                atomic_fetch_add_explicit(&queue->dequeue_count, 1,
                                          memory_order_relaxed);

                hp_clear(hp_head);
                hp_clear(hp_next);
                return data;
            }
        }
    }
}

/**
 * Check if queue is empty (approximate)
 *
 * Note: This is a "fuzzy" check - result may be stale immediately.
 *
 * @param queue  Queue
 * @return       True if appears empty
 */
bool ms_is_empty(ms_queue_t *queue) {
    ms_node_t *head = atomic_load_explicit(&queue->head, memory_order_acquire);
    ms_node_t *tail = atomic_load_explicit(&queue->tail, memory_order_acquire);

    if (head == tail) {
        ms_node_t *next = atomic_load_explicit(&head->next, memory_order_acquire);
        return (next == NULL);
    }

    return false;
}

/**
 * Get queue size (approximate)
 *
 * Returns enqueue_count - dequeue_count.
 * Note: Result may be negative temporarily due to races.
 *
 * @param queue  Queue
 * @return       Approximate size
 */
uint64_t ms_get_size(ms_queue_t *queue) {
    uint64_t enq = atomic_load_explicit(&queue->enqueue_count,
                                        memory_order_relaxed);
    uint64_t deq = atomic_load_explicit(&queue->dequeue_count,
                                        memory_order_relaxed);
    return (enq >= deq) ? (enq - deq) : 0;
}

/*******************************************************************************
 * TREIBER LOCK-FREE STACK (LIFO)
 ******************************************************************************/

/**
 * Initialize Treiber stack
 *
 * @param stack  Stack to initialize
 * @param hp     Hazard pointer domain
 */
void treiber_init(treiber_stack_t *stack, hp_domain_t *hp) {
    atomic_store(&stack->top, NULL);
    stack->hp = hp;

    /* Initialize statistics */
    atomic_store(&stack->push_count, 0);
    atomic_store(&stack->pop_count, 0);
}

/**
 * Push data onto stack (lock-free)
 *
 * ALGORITHM (Treiber, 1986):
 * 1. Allocate new node
 * 2. Loop:
 *    a. Read current top
 *    b. Set new_node->next = top
 *    c. Try CAS(top, old_top, new_node)
 *    d. If success: done
 *
 * LINEARIZATION POINT: CAS that updates top
 *
 * @param stack  Stack
 * @param data   Data to push
 * @param tid    Thread ID (unused, for API consistency)
 */
void treiber_push(treiber_stack_t *stack, void *data, int tid) {
    (void)tid;  /* Unused */

    /* Allocate new node */
    treiber_node_t *node = (treiber_node_t*)malloc(sizeof(treiber_node_t));
    node->data = data;

    while (true) {
        /* Read current top */
        treiber_node_t *old_top = atomic_load_explicit(&stack->top,
                                                        memory_order_acquire);

        /* Link new node to current top */
        atomic_store(&node->next, old_top);

        /* LINEARIZATION POINT: CAS to update top */
        if (atomic_compare_exchange_weak_explicit(
                &stack->top, &old_top, node,
                memory_order_release,   /* success: publish new top */
                memory_order_acquire))  /* failure: re-read top */
        {
            /* Success! */
            atomic_fetch_add_explicit(&stack->push_count, 1,
                                      memory_order_relaxed);
            return;
        }

        /* CAS failed, retry */
    }
}

/**
 * Pop data from stack (lock-free)
 *
 * ALGORITHM (Treiber, 1986):
 * 1. Loop:
 *    a. Read current top (protect with HP)
 *    b. If top == NULL: return NULL (empty)
 *    c. Read top->next
 *    d. Try CAS(top, old_top, top->next)
 *    e. If success: retire old top, return data
 *
 * LINEARIZATION POINT: CAS that updates top
 *
 * @param stack  Stack
 * @param tid    Thread ID
 * @return       Popped data, or NULL if empty
 */
void *treiber_pop(treiber_stack_t *stack, int tid) {
    /* Get hazard pointer */
    hazard_pointer_t *hp_top = hp_acquire(stack->hp, tid, 0);

    while (true) {
        /* Read current top (protect it) */
        treiber_node_t *old_top = hp_protect(hp_top, &stack->top);

        if (old_top == NULL) {
            /* Stack is empty */
            hp_clear(hp_top);
            return NULL;
        }

        /* Read next */
        treiber_node_t *next = atomic_load_explicit(&old_top->next,
                                                     memory_order_acquire);

        /* Read data BEFORE CAS (critical!) */
        void *data = old_top->data;

        /* LINEARIZATION POINT: CAS to update top */
        if (atomic_compare_exchange_weak_explicit(
                &stack->top, &old_top, next,
                memory_order_release,   /* success: publish new top */
                memory_order_acquire))  /* failure: re-read top */
        {
            /* Success! Retire old top */
            hp_retire(stack->hp, tid, old_top, free);

            atomic_fetch_add_explicit(&stack->pop_count, 1,
                                      memory_order_relaxed);

            hp_clear(hp_top);
            return data;
        }

        /* CAS failed, retry */
    }
}

/**
 * Check if stack is empty (approximate)
 *
 * @param stack  Stack
 * @return       True if appears empty
 */
bool treiber_is_empty(treiber_stack_t *stack) {
    treiber_node_t *top = atomic_load_explicit(&stack->top,
                                                memory_order_acquire);
    return (top == NULL);
}

/*******************************************************************************
 * PEDAGOGICAL EXAMPLES
 ******************************************************************************/

/**
 * Example: Concurrent queue operations
 *
 * Demonstrates MPMC queue with multiple producers and consumers.
 */
void example_lockfree_queue(void) {
    printf("=== Lock-Free Queue Example ===\n\n");

    /* Initialize hazard pointers and queue */
    hp_domain_t hp;
    hp_domain_init(&hp);

    ms_queue_t queue;
    ms_queue_init(&queue, &hp);

    /* Simulate thread 0 enqueuing */
    simulated_tid = 0;
    printf("Thread 0: Enqueuing 'A', 'B', 'C'\n");
    ms_enqueue(&queue, (void*)"A", 0);
    ms_enqueue(&queue, (void*)"B", 0);
    ms_enqueue(&queue, (void*)"C", 0);

    /* Simulate thread 1 dequeuing */
    simulated_tid = 1;
    printf("Thread 1: Dequeuing...\n");
    char *val1 = (char*)ms_dequeue(&queue, 1);
    printf("  Got: %s\n", val1 ? val1 : "NULL");

    /* Thread 0 enqueues more */
    simulated_tid = 0;
    printf("Thread 0: Enqueuing 'D'\n");
    ms_enqueue(&queue, (void*)"D", 0);

    /* Thread 1 dequeues all */
    simulated_tid = 1;
    while (!ms_is_empty(&queue)) {
        char *val = (char*)ms_dequeue(&queue, 1);
        printf("Thread 1: Dequeued %s\n", val ? val : "NULL");
    }

    printf("\nQueue size: %lu\n", ms_get_size(&queue));
    printf("Enqueues: %lu, Dequeues: %lu\n",
           atomic_load(&queue.enqueue_count),
           atomic_load(&queue.dequeue_count));

    printf("\n");
}

/**
 * Example: Concurrent stack operations
 *
 * Demonstrates LIFO stack with push/pop.
 */
void example_lockfree_stack(void) {
    printf("=== Lock-Free Stack Example ===\n\n");

    /* Initialize hazard pointers and stack */
    hp_domain_t hp;
    hp_domain_init(&hp);

    treiber_stack_t stack;
    treiber_init(&stack, &hp);

    /* Push operations */
    simulated_tid = 0;
    printf("Pushing: 1, 2, 3\n");
    treiber_push(&stack, (void*)(intptr_t)1, 0);
    treiber_push(&stack, (void*)(intptr_t)2, 0);
    treiber_push(&stack, (void*)(intptr_t)3, 0);

    /* Pop operations */
    printf("Popping...\n");
    while (!treiber_is_empty(&stack)) {
        intptr_t val = (intptr_t)treiber_pop(&stack, 0);
        printf("  Popped: %ld\n", val);
    }

    printf("\nStack operations: Push=%lu, Pop=%lu\n",
           atomic_load(&stack.push_count),
           atomic_load(&stack.pop_count));

    printf("\n");
}

/**
 * Example: Hazard pointer memory safety
 *
 * Demonstrates how hazard pointers prevent use-after-free.
 */
void example_hazard_pointers(void) {
    printf("=== Hazard Pointer Example ===\n\n");

    hp_domain_t hp;
    hp_domain_init(&hp);

    ms_queue_t queue;
    ms_queue_init(&queue, &hp);

    /* Enqueue many items to trigger retirement */
    simulated_tid = 0;
    printf("Enqueuing 150 items...\n");
    for (int i = 0; i < 150; i++) {
        int *data = (int*)malloc(sizeof(int));
        *data = i;
        ms_enqueue(&queue, data, 0);
    }

    /* Dequeue many items (will trigger HP scan at threshold) */
    printf("Dequeuing items...\n");
    int dequeued = 0;
    while (!ms_is_empty(&queue) && dequeued < 120) {
        int *data = (int*)ms_dequeue(&queue, 0);
        if (data) {
            free(data);  /* We can free data, HP protects nodes */
            dequeued++;
        }
    }

    printf("Dequeued %d items\n", dequeued);
    printf("Retired count for thread 0: %d\n",
           atomic_load(&hp.retire_counts[0]));
    printf("(HP scan triggered when retire count reached %d)\n",
           HP_RETIRE_THRESHOLD);

    /* Cleanup remaining items */
    while (!ms_is_empty(&queue)) {
        int *data = (int*)ms_dequeue(&queue, 0);
        if (data) free(data);
    }

    printf("\n");
}

/**
 * Example: ABA problem demonstration
 *
 * Shows how hazard pointers prevent ABA issues.
 */
void example_aba_problem(void) {
    printf("=== ABA Problem Example ===\n\n");

    printf("THE ABA PROBLEM:\n");
    printf("----------------\n");
    printf("Thread 1: Reads top = A\n");
    printf("Thread 1: [preempted]\n");
    printf("Thread 2: Pop A (top = B)\n");
    printf("Thread 2: Pop B (top = NULL)\n");
    printf("Thread 2: Push A (top = A again!)\n");
    printf("Thread 1: [resumes] CAS(top, A, ...) succeeds!\n");
    printf("          ^^^ WRONG! Top changed A→B→NULL→A\n\n");

    printf("SOLUTION WITH HAZARD POINTERS:\n");
    printf("-------------------------------\n");
    printf("Thread 1: Reads top = A\n");
    printf("Thread 1: Protects A with hazard pointer\n");
    printf("Thread 1: [preempted]\n");
    printf("Thread 2: Pop A (deferred - A is protected!)\n");
    printf("Thread 2: Retires A to reclamation list\n");
    printf("Thread 2: Pop B\n");
    printf("Thread 2: Push new_A\n");
    printf("Thread 1: [resumes] CAS(top, A, ...) sees A != new_A\n");
    printf("          ^^^ CORRECT! Pointers are distinct\n");
    printf("\nHazard pointers prevent freeing protected memory,\n");
    printf("ensuring pointer uniqueness and ABA safety.\n\n");
}

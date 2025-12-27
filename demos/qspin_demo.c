/**
 * @file qspin_demo.c
 * @brief Standalone queued spinlock demonstration
 *
 * Demonstrates the queued spinlock API without kernel dependencies.
 * Uses local stubs to show the calling convention.
 */

#include <stdio.h>
#include <stdint.h>

/* ═══════════════════════════════════════════════════════════════════════
 * LOCAL STUBS - Standalone demo without kernel dependencies
 * ═══════════════════════════════════════════════════════════════════════ */

struct spinlock {
    int locked;
    const char *name;
};

static void qspin_lock(struct spinlock *lk) {
    (void)lk;
    printf("[qspin] lock acquired: %s\n", lk->name);
}

static void qspin_unlock(struct spinlock *lk) {
    (void)lk;
    printf("[qspin] lock released: %s\n", lk->name);
}

static int qspin_trylock(struct spinlock *lk) {
    (void)lk;
    printf("[qspin] trylock succeeded: %s\n", lk->name);
    return 1;
}

/* ═══════════════════════════════════════════════════════════════════════
 * MAIN DEMONSTRATION
 * ═══════════════════════════════════════════════════════════════════════ */

static struct spinlock demo_lock = {.locked = 0, .name = "demo_lock"};

int main(void) {
    printf("═══════════════════════════════════════════════════════════\n");
    printf("Queued Spinlock Demo\n");
    printf("═══════════════════════════════════════════════════════════\n\n");

    printf("[demo] Attempting trylock...\n");
    if (qspin_trylock(&demo_lock)) {
        printf("[demo] Trylock succeeded, releasing...\n");
        qspin_unlock(&demo_lock);
    }

    printf("\n[demo] Acquiring lock normally...\n");
    qspin_lock(&demo_lock);
    printf("[demo] Critical section work...\n");
    qspin_unlock(&demo_lock);

    printf("\n═══════════════════════════════════════════════════════════\n");
    printf("Queued spinlock demo complete\n");
    printf("═══════════════════════════════════════════════════════════\n");

    return 0;
}

#include <stdio.h>
#include "qspinlock.h"

struct spinlock demo_lock;

void qspin_lock(struct spinlock *lk) { (void)lk; printf("qspin_lock called\n"); }
void qspin_unlock(struct spinlock *lk) { (void)lk; printf("qspin_unlock called\n"); }
int qspin_trylock(struct spinlock *lk) { (void)lk; printf("qspin_trylock called\n"); return 1; }

int main(void) {
    if (qspin_trylock(&demo_lock)) {
        qspin_unlock(&demo_lock);
    }
    qspin_lock(&demo_lock);
    qspin_unlock(&demo_lock);
    return 0;
}

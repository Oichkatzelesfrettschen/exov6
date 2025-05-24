#pragma once

#include "../spinlock.h"

void qspin_lock(struct spinlock *lk);
void qspin_unlock(struct spinlock *lk);
int qspin_trylock(struct spinlock *lk);

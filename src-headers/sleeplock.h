#pragma once
#include "spinlock.h"
struct sleeplock { int locked; struct spinlock lk; };
static inline void initsleeplock(struct sleeplock *lk, const char *name) { (void)lk; (void)name; }
static inline void acquiresleep(struct sleeplock *lk) { (void)lk; }
static inline void releasesleep(struct sleeplock *lk) { (void)lk; }

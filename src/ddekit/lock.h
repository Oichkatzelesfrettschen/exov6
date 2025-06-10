#ifndef _DDEKIT_LOCK_H
#define _DDEKIT_LOCK_H

#include "ddekit.h"

struct ddekit_lock;
typedef struct ddekit_lock *ddekit_lock_t;

/** Initialize a DDEKit unlocked lock. */
#define ddekit_lock_init ddekit_lock_init_unlocked

/** Initialize a lock in the unlocked state. */
void ddekit_lock_init_unlocked(ddekit_lock_t *mtx);

/** Initialize a lock in the locked state. */
void ddekit_lock_init_locked(ddekit_lock_t *mtx);

/** Destroy a previously initialized lock. */
void ddekit_lock_deinit(ddekit_lock_t *mtx);

/** Acquire a lock and block until available. */
void ddekit_lock_lock(ddekit_lock_t *mtx);

/** Try to acquire a lock without blocking. */
int ddekit_lock_try_lock(ddekit_lock_t *mtx);

/** Release a previously acquired lock. */
void ddekit_lock_unlock(ddekit_lock_t *mtx);

/** Return the identifier of the current lock owner. */
int ddekit_lock_owner(ddekit_lock_t *mtx);

#endif

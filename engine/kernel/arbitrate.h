#ifndef ARBITRATE_H
#define ARBITRATE_H

#include "types.h"
#include <stdint.h>
#include <stdatomic.h>

#ifdef __cplusplus
extern "C" {
#endif

struct arbitrate_entry {
  uint32_t type;
  uint32_t resource_id;
  uint32_t owner;
};

struct arbitrate_table {
  struct spinlock lock;
  struct arbitrate_entry entries[16];
};

typedef int (*arbitrate_policy_t)(uint32_t type, uint32_t resource_id,
                                  uint32_t current_owner, uint32_t new_owner);

void arbitrate_init(arbitrate_policy_t policy);
void arbitrate_use_table(struct arbitrate_table *t);
void arbitrate_register_policy(arbitrate_policy_t policy);
#ifdef __cplusplus
}
#endif

#endif // ARBITRATE_H

#ifndef SPINLOCK_H
#define SPINLOCK_H

#include <stdatomic.h>

struct spinlock {
  atomic_flag flag;
};

static inline void spinlock_init(struct spinlock *lock) {
  atomic_flag_clear(&lock->flag);
}

static inline void spinlock_lock(struct spinlock *lock) {
  while (atomic_flag_test_and_set(&lock->flag)) { /* spin */ }
}

static inline void spinlock_unlock(struct spinlock *lock) {
  atomic_flag_clear(&lock->flag);
}

#endif // SPINLOCK_H

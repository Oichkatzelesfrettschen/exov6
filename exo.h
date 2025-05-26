#ifndef EXO_H
#define EXO_H
#include "engine/include/types.h"

typedef struct hash256 {
  uint64_t parts[4];
} hash256_t;

typedef struct exo_cap {
  uint32_t pa;
  uint32_t id;
  uint32_t rights;
  uint32_t owner;
  hash256_t auth_tag;
} exo_cap;

typedef struct exo_blockcap {
  uint32_t dev;
  uint32_t blockno;
  uint32_t rights;
  uint32_t owner;
} exo_blockcap;

#ifdef EXO_KERNEL
exo_cap exo_alloc_page(void);
[[nodiscard]] int exo_unbind_page(exo_cap c);
exo_cap cap_new(uint32_t id, uint32_t rights, uint32_t owner);
int cap_verify(exo_cap c);
#endif

#endif /* EXO_H */

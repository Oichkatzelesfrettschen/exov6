#ifndef EXO_H
#define EXO_H
#ifdef __cplusplus
extern "C" {
#endif
#include "types.h"

typedef struct hash256 {
  uint64 parts[4];
} hash256_t;

typedef struct exo_cap {
  uint pa;
  uint id;
  uint rights;
  uint owner;
  hash256_t auth_tag;
} exo_cap;

typedef struct exo_blockcap {
  uint dev;
  uint blockno;
  uint rights;
  uint owner;
} exo_blockcap;

#ifdef EXO_KERNEL
exo_cap exo_alloc_page(void);
int exo_unbind_page(exo_cap c);
exo_cap cap_new(uint id, uint rights, uint owner);
int cap_verify(exo_cap c);
#endif

#ifdef __cplusplus
}
#endif
#endif // EXO_H

#ifndef EXO_H
#define EXO_H
#include "types.h"

typedef struct exo_cap {
  uint pa;
  uint owner;
} exo_cap;

typedef struct exo_blockcap {
  uint dev;
  uint blockno;
  uint rights;
  uint owner;
} exo_blockcap;

exo_cap exo_alloc_page(void);
int exo_unbind_page(exo_cap c);
int exo_alloc_block(uint dev, exo_blockcap *cap);
int exo_bind_block(exo_blockcap *cap, void *data, int write);

#endif // EXO_H

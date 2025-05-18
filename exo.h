#ifndef EXO_H
#define EXO_H
#include "types.h"

typedef struct exo_cap {
  uint pa;
} exo_cap;

exo_cap exo_alloc_page(void);
int exo_unbind_page(exo_cap c);

#endif // EXO_H

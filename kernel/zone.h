#ifndef ZONE_H
#define ZONE_H

#include "spinlock.h"
#include <stddef.h>

/* Forward declarations */
struct zone;
typedef struct exo_cap exo_cap;

// Header stored before each allocated object
struct zone_obj {
  struct zone_obj *next;
  int zone_id;
};

struct slab {
  struct slab *next;
  struct zone *zone;
  int zone_id;
  exo_cap cap;
  struct zone_obj *free;
  int inuse;
};

typedef struct zone {
  struct spinlock lock;
  size_t obj_size;
  int zone_id;
  struct slab *slabs;
} zone_t;

void zone_init(zone_t *z, size_t obj_size, char *name);
void *zalloc(zone_t *z);
void zfree(zone_t *z, void *ptr);
void zone_dump(zone_t *z);

#endif // ZONE_H

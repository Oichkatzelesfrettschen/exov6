#include "zone.h"
#include "defs.h"
#include "mmu.h"
#include "memlayout.h"

static int next_zone_id = 1;

void
zone_init(zone_t *z, size_t obj_size, char *name)
{
  initlock(&z->lock, name);
  z->obj_size = obj_size;
  z->slabs = 0;
  z->zone_id = __sync_fetch_and_add(&next_zone_id, 1);
}

static struct slab*
new_slab(zone_t *z)
{
  struct slab *s = (struct slab*)kalloc();
  if(!s)
    return 0;
  s->zone = z;
  s->zone_id = z->zone_id;
  s->inuse = 0;
  s->next = z->slabs;
  z->slabs = s;

  s->free = 0;
  size_t hdr = sizeof(struct slab);
  size_t objsz = sizeof(struct zone_obj) + z->obj_size;
  int n = (PGSIZE - hdr) / objsz;
  char *p = (char*)s + hdr;
  for(int i=0;i<n;i++){
    struct zone_obj *o = (struct zone_obj*)p;
    o->zone_id = z->zone_id;
    o->next = s->free;
    s->free = o;
    p += objsz;
  }
  return s;
}

void *
zalloc(zone_t *z)
{
  acquire(&z->lock);
  struct slab *s;
  for(s = z->slabs; s; s = s->next){
    if(s->free)
      break;
  }
  if(!s){
    s = new_slab(z);
    if(!s){
      release(&z->lock);
      return 0;
    }
  }
  struct zone_obj *o = s->free;
  s->free = o->next;
  s->inuse++;
  release(&z->lock);
  o->zone_id = z->zone_id;
  return (void*)(o + 1);
}

void
zfree(zone_t *z, void *ptr)
{
  if(!ptr)
    return;
  struct zone_obj *o = ((struct zone_obj*)ptr) - 1;
  struct slab *s = (struct slab*)((uintptr_t)o & ~(PGSIZE-1));
  if(s->zone_id != z->zone_id || o->zone_id != z->zone_id){
    zone_dump(z);
    panic("zone_id mismatch");
  }

  acquire(&z->lock);
  o->next = s->free;
  s->free = o;
  s->inuse--;
  release(&z->lock);
}

void
zone_dump(zone_t *z)
{
  cprintf("zone %d size %d\n", z->zone_id, (int)z->obj_size);
  for(struct slab *s = z->slabs; s; s = s->next){
    int free = 0;
    for(struct zone_obj *o = s->free; o; o = o->next)
      free++;
    cprintf(" slab %p id %d inuse %d free %d\n", s, s->zone_id, s->inuse, free);
  }
}

#ifndef EXOV6_MM_H
#define EXOV6_MM_H

#include <types.h>
#include <memlayout.h>
#include <exov6_interface.h>

struct PageInfo {
    struct PageInfo *next;
    uint16_t ref_count;
    uint16_t owner_env;
    label_t  label;
};

// Core Map Accessors
extern struct PageInfo *pages;
// Using KERNBASE/PGSIZE from memlayout/param
#define PA2PAGE(pa) (&pages[((uint64)pa - KERNBASE) / PGSIZE])
#define PAGE2PA(pp) (KERNBASE + ((pp - pages) * PGSIZE))

#endif

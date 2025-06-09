#ifndef _DDEKIT_INITCALL_H
#define _DDEKIT_INITCALL_H
#include "ddekit.h"
#include "attribs.h"

typedef void (*ddekit_initcall_t)(void);

struct __ddekit_initcall_s {
  ddekit_initcall_t func;
  int prio;
  struct __ddekit_initcall_s *next;
};

/**
 * @brief Register a function to be executed during initialization.
 *
 * @param dis Descriptor describing the initcall function and priority.
 */
void __ddekit_add_initcall(struct __ddekit_initcall_s *dis);

/* Define a function to be a DDEKit initcall.
 * This is the right place to place Linux' module_init functions & Co.
 */
#define DDEKIT_INITCALL(fn) DDEKIT_CTOR(fn, 1)

#define DDEKIT_CTOR(fn, prio)                                                  \
  static void __attribute__((used))                                            \
  __attribute__((constructor)) __ddekit_initcall_##fn() {                      \
    static struct __ddekit_initcall_s dis = {(ddekit_initcall_t)fn, prio, 0};  \
    __ddekit_add_initcall(&dis);                                               \
  }

/**
 * @brief Invoke all registered initialization callbacks in order.
 */
void ddekit_do_initcalls(void);

#endif

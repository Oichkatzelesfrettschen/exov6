#pragma once
#include <types.h>
#include "user.h"

/* Lightweight capability wrapper used by libSMK. */
typedef struct {
  uint16_t id;
} cap_t;

static inline void borrow(cap_t c) { cap_inc(c.id); }
static inline void drop(cap_t c) { cap_dec(c.id); }

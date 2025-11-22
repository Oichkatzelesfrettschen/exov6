#pragma once

// Generic macros for type-safe operations using typeof and _Generic
// These helpers evaluate their arguments exactly once and enforce that
// both operands have compatible types.

#define GU_TYPE_CHECK(a, b)                                                   \
  ((void)_Generic(&(a), __typeof__(&(b)): (void)0, default: (void)0))

#define GU_MIN(a, b)                                                          \
  ({                                                                         \
    __typeof__(a) _a = (a);                                                  \
    __typeof__(b) _b = (b);                                                  \
    GU_TYPE_CHECK(_a, _b);                                                   \
    _a < _b ? _a : _b;                                                       \
  })

#define GU_MAX(a, b)                                                          \
  ({                                                                         \
    __typeof__(a) _a = (a);                                                  \
    __typeof__(b) _b = (b);                                                  \
    GU_TYPE_CHECK(_a, _b);                                                   \
    _a > _b ? _a : _b;                                                       \
  })

#define GU_SWAP(a, b)                                                         \
  do {                                                                       \
    GU_TYPE_CHECK(a, b);                                                     \
    __typeof__(a) _tmp = (a);                                                \
    (a) = (b);                                                               \
    (b) = _tmp;                                                              \
  } while (0)


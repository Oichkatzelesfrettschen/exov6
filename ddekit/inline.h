#include <compiler_attrs.h>

#if EXO_HAS_ATTR(always_inline)
# define DDEKIT_INLINE __inline__ __attribute__((always_inline))
#else
# define DDEKIT_INLINE __inline__
#endif


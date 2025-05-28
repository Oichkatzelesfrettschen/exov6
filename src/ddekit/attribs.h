#ifndef _DDEKIT_ATTRIBS_H
#define _DDEKIT_ATTRIBS_H

#include <compiler_attrs.h>

#ifdef __ACK__


#else

#if EXO_HAS_ATTR(used)
# define DDEKIT_USED __attribute__((used))
#else
# define DDEKIT_USED
#endif

#if EXO_HAS_ATTR(constructor)
# define DDEKIT_CONSTRUCTOR __attribute__((constructor))
#else
# define DDEKIT_CONSTRUCTOR
#endif


#define DDEKIT_PUBLIC PUBLIC
#define DDEKIT_PRIVATE static
#endif
#endif

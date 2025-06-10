#include "types.h"
#include <string.h>

// Like strncpy but guaranteed to NUL-terminate.
char *
safestrcpy(char *s, const char *t, size_t n)
{
  char *os = s;
  if (n <= 0)
    return os;
  while (--n > 0 && (*s++ = *t++) != 0)
    ;
  *s = 0;
  return os;
}

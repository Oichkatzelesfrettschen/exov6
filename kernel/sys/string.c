#include <types.h>
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

size_t
strlen(const char *s)
{
  size_t n;
  for (n = 0; s[n]; n++)
    ;
  return n;
}

int
strncmp(const char *p, const char *q, size_t n)
{
  while (n > 0 && *p && *p == *q)
    n--, p++, q++;
  if (n == 0)
    return 0;
  return (uint8_t)*p - (uint8_t)*q;
}

char *
strncpy(char *s, const char *t, size_t n)
{
  char *os = s;
  while (n-- > 0 && (*s++ = *t++) != 0)
    ;
  while (n-- > 0)
    *s++ = 0;
  return os;
}

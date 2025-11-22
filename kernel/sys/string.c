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
strncmp(const char *s1, const char *s2, size_t n)
{
  while (n > 0 && *s1 && *s1 == *s2)
    n--, s1++, s2++;
  if (n == 0)
    return 0;
  return (uint8_t)*s1 - (uint8_t)*s2;
}

char *
strncpy(char *dst, const char *src, size_t n)
{
  char *os = dst;
  while (n-- > 0 && (*dst++ = *src++) != 0)
    ;
  while (n-- > 0)
    *dst++ = 0;
  return os;
}

#include "types.h"
#include "stat.h"
#include "fcntl.h"
#include "user.h"
#include <string.h>
#include <unistd.h>

/* Declare system call prototypes to avoid implicit declarations */
int open(const char *path, int flags, ...);
ssize_t read(int fd, void *buf, size_t n);
int fstat(int fd, struct stat *st);
int close(int fd);

char *strcpy(char *s, const char *t) {
  char *os;

  os = s;
  while ((*s++ = *t++) != 0)
    ;
  return os;
}

int strcmp(const char *p, const char *q) {
  while (*p && *p == *q)
    p++, q++;
  return (uint8_t)*p - (uint8_t)*q;
}

size_t strlen(const char *s) {
  int n;

  for (n = 0; s[n]; n++)
    ;
  return n;
}

void *memset(void *dst, int c, size_t n) { return __builtin_memset(dst, c, n); }

char *strchr(const char *s, char c) {
  for (; *s; s++)
    if (*s == c)
      return (char *)s;
  return 0;
}

char *gets(char *buf, size_t max) {
  size_t i, cc;
  char c;

  for (i = 0; i + 1 < max;) {
    cc = read(0, &c, 1);
    if (cc < 1)
      break;
    buf[i++] = c;
    if (c == '\n' || c == '\r')
      break;
  }
  buf[i] = '\0';
  return buf;
}

int stat(const char *n, struct stat *st) {
  int fd;
  int r;

  fd = open(n, O_RDONLY);
  if (fd < 0)
    return -1;
  r = fstat(fd, st);
  close(fd);
  return r;
}

int atoi(const char *s) {
  int n;

  n = 0;
  while ('0' <= *s && *s <= '9')
    n = n * 10 + *s++ - '0';
  return n;
}

void *memmove(void *vdst, const void *vsrc, size_t n) {
  return __builtin_memmove(vdst, vsrc, n);
}

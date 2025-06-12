#include <stdio.h>
#include "math_core.h"
#include "user.h"

int main(void) {
  unsigned n = 100;
#ifdef __BITINT_MAXWIDTH__
  uint256_t val = fib_big(n);
  printf("fib_big(%u) = 0x", n);
  for (int i = 3; i >= 0; i--) {
    unsigned long long part = (unsigned long long)(val >> (i * 64));
    printf("%016llx", part);
  }
  printf("\n");
#else
  printf("fib_big(%u) = %llu (fallback)\n", n, (unsigned long long)fib_big(n));
#endif
  return 0;
#ifdef __BITINT_MAXWIDTH__
  static void print_big_hex(fib_big_t x) {
    char buf[65];
    for (int i = 0; i < 64; i++) {
      int nib = (int)(x & 0xf);
      buf[63 - i] = "0123456789ABCDEF"[nib];
      x >>= 4;
    }
    buf[64] = '\0';
    int start = 0;
    while (start < 63 && buf[start] == '0')
      start++;
    printf(1, "fib(200) = 0x%s\n", &buf[start]);
  }
#endif

  int main(void) {
    uint32_t n = 200;
#ifdef __BITINT_MAXWIDTH__
    fib_big_t val = fib_big(n);
    print_big_hex(val);
#else
    uint64_t val = fib_big(n);
    printf(1, "fib(%u) = %lx\n", n, val);
#endif
    return 0;
  }

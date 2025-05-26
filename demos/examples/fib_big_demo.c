#include "math_core.h"
#include "user.h"

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

#include "types.h"
#include "stat.h"
#include "user.h"
#include "math_core.h"

int
main(int argc, char *argv[])
{
  if(argc < 2){
    printf(1, "usage: phi mu [guard]\n");
    exit();
  }
  size_t mu = atoi(argv[1]);
  size_t guard = 0;
  if(argc > 2)
    guard = atoi(argv[2]);

  size_t s = phi_ring_size(mu, guard);
  printf(1, "phi_ring_size(%d,%d)=%d\n", mu, guard, s);

  uint k = 10;
  uint m = 6;
  uint fibk = fib(k);
  uint gcdv = gcd(fibk, 1U << m);
  printf(1, "gcd(Fib(%d),2^%d)=%d\n", k, m, gcdv);

  exit();
}


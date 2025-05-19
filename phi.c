#include "user.h"
#include "math_core.h"

int
main(int argc, char *argv[])
{
  int n = 10;
  int m = 5;
  if(argc > 1)
    n = atoi(argv[1]);
  if(argc > 2)
    m = atoi(argv[2]);

  int f = fib(n);
  int g = gcd(f, 1 << m);

  printf(1, "fib(%d) = %d\n", n, f);
  printf(1, "gcd(fib(%d), 1<<%d) = %d\n", n, m, g);
  exit();
}

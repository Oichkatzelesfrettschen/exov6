#include "types.h"
#include "sys/stat.h"
#include "user.h"

// compute nth Fibonacci number
// fib(n) is even iff n is divisible by 3
static int
fib(int n)
{
  if(n <= 0)
    return 0;
  if(n == 1 || n == 2)
    return 1;
  int a = 1, b = 1, c;
  for(int i = 3; i <= n; i++){
    c = a + b;
    a = b;
    b = c;
  }
  return b;
}

static int
pow2(int m)
{
  return 1 << m;
}

static int
gcd(int a, int b)
{
  int t;
  while(b != 0){
    t = a % b;
    a = b;
    b = t;
  }
  return a;
}

static void
demo(void)
{
  // pairs of (n, m) to demonstrate gcd values
  int pairs[][2] = { {3,2}, {5,4}, {9,1}, {7,3} };
  int npairs = sizeof(pairs)/sizeof(pairs[0]);
  for(int i = 0; i < npairs; i++){
    int n = pairs[i][0];
    int m = pairs[i][1];
    int f = fib(n);
    int p = pow2(m);
    int g = gcd(f, p);
    printf(1, "n=%d fib=%d m=%d 2^m=%d gcd=%d\n", n, f, m, p, g);
  }
}

int
main(int argc, char *argv[])
{
  if(argc == 1){
    demo();
    exit();
  }

  if(argc != 3){
    printf(2, "Usage: phi n m\n");
    exit();
  }

  int n = atoi(argv[1]);
  int m = atoi(argv[2]);
  int f = fib(n);
  int p = pow2(m);
  int g = gcd(f, p);
  printf(1, "fib(%d)=%d 2^%d=%d gcd=%d\n", n, f, m, p, g);
  exit();
}

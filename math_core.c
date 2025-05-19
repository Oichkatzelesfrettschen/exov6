#include "types.h"
#include "user.h"

int
gcd(int a, int b)
{
  int t;
  while(b != 0){
    t = b;
    b = a % b;
    a = t;
  }
  return a;
}

int
fib(int n)
{
  int a, b, i, t;
  if(n <= 0)
    return 0;
  a = 0;
  b = 1;
  for(i = 1; i < n; i++){
    t = a + b;
    a = b;
    b = t;
  }
  return b;
}

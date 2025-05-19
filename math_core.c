#include "math_core.h"

size_t
phi_ring_size(size_t mu, size_t guard)
{
  double val = PHI_CONST * (double)mu;
  size_t ceilv = (size_t)val;
  if(val > (double)ceilv)
    ceilv++;
  return ceilv + guard;
}

uint
fib(uint n)
{
  uint a = 0;
  uint b = 1;
  for(uint i = 0; i < n; i++){
    uint t = a + b;
    a = b;
    b = t;
  }
  return a;
}

uint
gcd(uint a, uint b)
{
  while(b != 0){
    uint t = b;
    b = a % b;
    a = t;
  }
  return a;
}


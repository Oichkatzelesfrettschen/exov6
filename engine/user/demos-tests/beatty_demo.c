#include <stdio.h>
#include "math_core.h"

static double alpha;
static double beta;
static int na = 1;
static int nb = 1;

static void task_a(int slice) { printf("A slice %d\n", slice); }
static void task_b(int slice) { printf("B slice %d\n", slice); }

static void schedule_step(int slice) {
  double va = alpha * (double)na;
  double vb = beta * (double)nb;
  if ((int)va < (int)vb) {
    task_a(slice);
    na++;
  } else {
    task_b(slice);
    nb++;
  }
}

int main(int argc, char **argv) {
  (void)argc;
  (void)argv;
#ifdef HAVE_DECIMAL_FLOAT
  alpha = dec64_to_double(phi());
#else
  alpha = phi();
#endif
  beta = alpha / (alpha - 1.0);
  for (int i = 1; i <= 10; i++)
    schedule_step(i);
  return 0;
}

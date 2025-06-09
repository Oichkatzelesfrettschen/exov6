#include <altivec.h>

typedef __vector unsigned int v4u32;

/** Validate availability of AltiVec instructions. */
int cap_validate_altivec(void) {
  v4u32 z = vec_splats((unsigned int)0);
  return (int)vec_extract(z, 0);
}

/** Minimal DAG processing example for AltiVec. */
void dag_process_altivec(void) {
  v4u32 a = vec_splats((unsigned int)1);
  v4u32 r = vec_add(a, a);
  (void)r;
}

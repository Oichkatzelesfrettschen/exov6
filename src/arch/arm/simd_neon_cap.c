#include <arm_neon.h>

/** Validate availability of NEON instructions. */
int cap_validate_neon(void) {
  uint8x8_t z = vdup_n_u8(0);
  return vget_lane_u8(z, 0);
}

/** Minimal DAG processing example for NEON. */
void dag_process_neon(void) {
  uint8x8_t a = vdup_n_u8(1);
  uint8x8_t r = vadd_u8(a, a);
  (void)r;
}

/**
 * @file picokernel.c
 * @brief Minimal exokernel core with capability management
 * Replaces MCU-specific code with pure exokernel abstractions
 */

#include "defs.h"
#include "cap.h"
#include "exo.h"
#include <types.h>

/* Exokernel capability structure - simplified for picokernel */
struct exo_simple_cap {
    cap_id_t cap_id;      /* Capability table ID */
    uint32_t resource;    /* Resource identifier */
    uint32_t rights;      /* Access rights */
};

static struct exo_simple_cap exo_table[64];  /* Small capability table */

uint32_t cap_alloc_gpio(uintptr_t addr) {
  table[0].addr = addr;
  return 0;
}

uintptr_t cap_get_addr(uint32_t id) { return table[id].addr; }

extern int blink_main(void);

int main(void) {
  cap_alloc_gpio(GPIO_BASE);
  blink_main();
  while (1)
    ;
}

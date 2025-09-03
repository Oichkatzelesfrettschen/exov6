#include "arch/mcu/gpio.h"
#include <types.h>
#include "cap.h"

struct simple_cap {
  uintptr_t addr;
};

static struct simple_cap table[1];

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

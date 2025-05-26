#include "arch/mcu/gpio.h"
#include <stdint.h>

extern uintptr_t cap_get_addr(uint32_t id);

int blink_main(void) {
  volatile uint32_t *gpio = (uint32_t *)cap_get_addr(0);
  for (;;) {
    gpio_toggle();
    for (volatile int i = 0; i < 100000; i++)
      ;
  }
  return 0;
}

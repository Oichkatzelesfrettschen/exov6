#pragma once
#include <stdint.h>

#define GPIO_BASE 0x50000000u
#define LED_PIN_MASK 0x1

static inline void gpio_toggle(void) {
  volatile uint32_t *odr = (uint32_t *)(GPIO_BASE);
  *odr ^= LED_PIN_MASK;
}

#include "libos/baremetal.h"
#include <arch_x86_64.h>

/* Simple wrappers around the architecture-specific port I/O helpers. */

uint8_t bm_inb(uint16_t port) { return inb(port); }

void bm_outb(uint16_t port, uint8_t data) { outb(port, data); }


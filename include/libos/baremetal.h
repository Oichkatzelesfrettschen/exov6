#pragma once
#include <stdint.h>

/* Basic port I/O helpers for baremetal interaction. */

/* Read a byte from the specified port. */
uint8_t bm_inb(uint16_t port);

/* Write a byte to the specified port. */
void bm_outb(uint16_t port, uint8_t data);


// user/uart_driver.c

#include <sys/types.h>

// Serial Line Status Register (LSR) Offset
#define UART_LSR 5
// Transmit Holding Register Empty bit
#define UART_LSR_THRE 0x20

// Placeholder for UART Virtual Address.
// In a real scenario, this would be a mapped address (e.g. via SYS_page_map or SYS_exo_alloc_ioport mapping).
#define UART_VADDR 0x40000000

void uart_putc(volatile uint8_t *uart_base, char c) {
    // 1. Wait for the hardware to be ready (Spin)
    // Note: In a real Exokernel, if this takes too long, we would Yield().
    while ((uart_base[UART_LSR] & UART_LSR_THRE) == 0)
        ;

    // 2. Write the character
    uart_base[0] = c;
}

int main() {
    // ... map hardware ...
    // In a real Exokernel, we would map the UART device here.
    volatile uint8_t *uart = (uint8_t*)UART_VADDR;

    // "Hello World" directly to hardware
    char *msg = "Exokernel UART Driver is Live!\n";
    for(int i = 0; msg[i]; i++) {
        uart_putc(uart, msg[i]);
    }

    return 0;
}

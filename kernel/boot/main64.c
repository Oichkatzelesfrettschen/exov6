#include <types.h>

extern int main(void);

/* Direct serial port I/O for early boot messages (COM1 = 0x3F8) */
#define COM1_PORT 0x3F8

static inline void outb(unsigned short port, unsigned char val) {
    __asm__ volatile("outb %0, %1" : : "a"(val), "Nd"(port));
}

static inline unsigned char inb(unsigned short port) {
    unsigned char ret;
    __asm__ volatile("inb %1, %0" : "=a"(ret) : "Nd"(port));
    return ret;
}

/* Early serial output - works before console initialization */
static void early_serial_putc(char c) {
    /* Wait for transmit holding register empty */
    while ((inb(COM1_PORT + 5) & 0x20) == 0)
        ;
    outb(COM1_PORT, c);
}

static void early_serial_puts(const char *s) {
    while (*s) {
        if (*s == '\n')
            early_serial_putc('\r');
        early_serial_putc(*s++);
    }
}

/* Boot success marker - called after kernel initialization completes */
void boot_success_marker(void) {
    early_serial_puts("\n=== KERNEL_BOOT_SUCCESS ===\n");
}

int main64(void) {
    /* Early boot message for QEMU serial capture */
    early_serial_puts("main64: entering kernel\n");
    return main();
}

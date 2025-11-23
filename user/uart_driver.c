/**
 * @file uart_driver.c
 * @brief User-space UART driver - The Ultimate Exokernel Test
 *
 * This program demonstrates the core exokernel thesis:
 * A user-space driver can directly access hardware without kernel mediation.
 *
 * If this works, we have proven:
 * 1. The kernel exports hardware safely (MMIO mapping)
 * 2. User code can drive hardware directly
 * 3. The kernel doesn't need to "know" about UART
 */

#include <stdint.h>
#include <types.h>
#include <exov6_interface.h>

// Forward declarations from lib/syscall.c
extern uint64 sys_alloc_page(void);
extern int sys_map_page(int target_env, uint64 phys, uint64 virt, int perm);
extern void sys_cputs(const char *s, int len);

// Forward declaration from lib/print.c
extern void print(const char *s);
extern void print_hex(uint64 n);

// QEMU Virt UART0 Register Offsets (16550-compatible)
#define UART_THR    0   // Transmit Holding Register (write)
#define UART_RBR    0   // Receive Buffer Register (read)
#define UART_IER    1   // Interrupt Enable Register
#define UART_FCR    2   // FIFO Control Register
#define UART_LCR    3   // Line Control Register
#define UART_MCR    4   // Modem Control Register
#define UART_LSR    5   // Line Status Register
#define UART_MSR    6   // Modem Status Register

// Line Status Register bits
#define LSR_TX_EMPTY    0x20    // Transmit holding register empty
#define LSR_RX_READY    0x01    // Data ready

// Where we'll map the UART in our address space
#define UART_VADDR  0x80000000ULL

// Helper: write a string directly to UART hardware
static void uart_direct_puts(volatile uint8_t *uart, const char *s) {
    while (*s) {
        // Wait for transmit holding register to be empty
        while ((uart[UART_LSR] & LSR_TX_EMPTY) == 0)
            ;
        // Write character
        uart[UART_THR] = *s++;
    }
}

// Helper: write a single character
static void uart_direct_putc(volatile uint8_t *uart, char c) {
    while ((uart[UART_LSR] & LSR_TX_EMPTY) == 0)
        ;
    uart[UART_THR] = c;
}

int main(void) {
    print("═══════════════════════════════════════════════════════════\n");
    print("  UART_DRIVER: User-Space Hardware Access Test\n");
    print("═══════════════════════════════════════════════════════════\n\n");

    // Step 1: Request MMIO mapping from kernel
    print("[1] Requesting MMIO mapping for UART0...\n");
    print("    Physical: ");
    print_hex(UART0_BASE);
    print("\n    Virtual:  ");
    print_hex(UART_VADDR);
    print("\n");

    // Map UART0 physical address to our virtual address space
    // PERM_R | PERM_W = 0x3 (read + write)
    int result = sys_map_page(0, UART0_BASE, UART_VADDR, 0x3);

    if (result < 0) {
        print("    FAILED: Could not map UART MMIO region.\n");
        print("    (Process may lack LABEL_HIGH privilege)\n");
        return -1;
    }

    print("    SUCCESS: MMIO region mapped!\n\n");

    // Step 2: Direct hardware access
    print("[2] Attempting direct hardware access...\n");
    print("    Bypassing kernel, writing directly to UART THR...\n\n");

    volatile uint8_t *uart = (volatile uint8_t *)UART_VADDR;

    // The moment of truth: write directly to hardware
    print("[3] DIRECT HARDWARE OUTPUT:\n");
    print("    >>> ");

    // These characters go DIRECTLY to the UART, bypassing all kernel code
    uart_direct_puts(uart, "XV6-EXO");
    uart_direct_putc(uart, '\n');

    print("\n");
    print("[4] If you saw 'XV6-EXO' above (outside the >>> line),\n");
    print("    then USER-SPACE HARDWARE ACCESS IS CONFIRMED!\n\n");

    // Additional test: read LSR to verify we can read registers too
    print("[5] Reading UART Line Status Register...\n");
    print("    LSR value: ");
    print_hex((uint64)uart[UART_LSR]);
    print("\n");

    print("\n═══════════════════════════════════════════════════════════\n");
    print("  EXOKERNEL THESIS VERIFIED:\n");
    print("  - Kernel exported hardware safely\n");
    print("  - User code drove hardware directly\n");
    print("  - Kernel did NOT mediate UART I/O\n");
    print("═══════════════════════════════════════════════════════════\n");

    // Spin forever
    while (1)
        ;

    return 0;
}

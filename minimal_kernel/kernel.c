/* Minimal kernel for testing */

// VGA text mode buffer
volatile unsigned char* video = (unsigned char*)0xB8000;
int cursor_pos = 0;

void putchar(char c) {
    if (c == '\n') {
        cursor_pos = (cursor_pos / 160 + 1) * 160;
    } else {
        video[cursor_pos++] = c;
        video[cursor_pos++] = 0x07; // Light gray on black
    }
}

void puts(const char* str) {
    while (*str) {
        putchar(*str++);
    }
}

void kernel_main(void) {
    // Clear screen
    for (int i = 0; i < 80 * 25 * 2; i++) {
        video[i] = 0;
    }
    
    puts("FeuerBird Exokernel v6\n");
    puts("======================\n\n");
    puts("Minimal kernel running successfully!\n");
    puts("Ready for QEMU testing.\n");
    
    // Halt
    while (1) {
        __asm__ __volatile__("hlt");
    }
}
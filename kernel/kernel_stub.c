// Minimal kernel stub for testing
int main() {
    // Print to serial port
    char *msg = "ExoKernel v6 POSIX-2024 Compliant OS\n";
    char *p = msg;
    while (*p) {
        __asm__ volatile("outb %0, %w1" : : "a"(*p), "Nd"(0x3f8));
        p++;
    }
    
    // Halt
    while(1) {
        __asm__ volatile("hlt");
    }
    
    return 0;
}

// Entry point
void _start() {
    main();
}

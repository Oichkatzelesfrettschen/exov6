// Minimal kernel stub for testing
void main() {
    // Print to serial port
    char *msg = "ExoKernel v6 POSIX-2024 Compliant OS\n";
    char *p = msg;
    while (*p) {
        asm volatile("outb %0, %1" : : "a"(*p), "d"(0x3f8));
        p++;
    }
    
    // Halt
    while(1) {
        asm volatile("hlt");
    }
}

// Entry point
void _start() {
    main();
}

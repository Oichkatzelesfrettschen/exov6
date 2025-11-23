// user/init.c - The First Contractor
// Phase 3: Exokernel Bootstrap with LibOS

#include <types.h>

// LibOS print functions (from lib/print.c)
extern void print(const char *s);
extern void print_hex(uint64 n);
extern void print_uint(uint64 n);

// Memory allocator (from lib/umalloc.c)
extern void* malloc(uint64 size);

int main(void) {
    print("EXOV6: SYSTEM ONLINE.\n");
    print("Hello from the Lattice.\n");
    print("\n");

    // Test the allocator
    print("Testing malloc... ");
    void *p = malloc(4096);
    if (p) {
        print("SUCCESS at ");
        print_hex((uint64)p);
        print("\n");
    } else {
        print("FAILED\n");
    }

    print("\n");
    print("=== EXOV6 BOOTSTRAP COMPLETE ===\n");
    print("Entering idle loop...\n");

    // Idle loop
    while(1)
        ;

    return 0;
}

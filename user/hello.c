/**
 * @file hello.c
 * @brief Simple Hello World Program (Phase 10 Test Target)
 *
 * This is a minimal program used to test ELF loading.
 * It prints a message and exits.
 *
 * When compiled, this becomes an ELF executable that can be:
 *   1. Stored on the file system
 *   2. Read by the file server
 *   3. Loaded by the ELF loader
 *   4. Executed via sys_env_run()
 */

#include <stdint.h>
#include <types.h>
#include <exov6_interface.h>

/* LibOS print function */
extern void print(const char *s);
extern void print_hex(uint64_t n);

/* LibOS initialization */
extern void libos_exception_init(void);

int main(void)
{
    print("\n");
    print("============================================\n");
    print("  HELLO FROM A LOADED ELF EXECUTABLE!\n");
    print("============================================\n");
    print("\n");
    print("This program was:\n");
    print("  1. Read from disk (via fs_srv IPC)\n");
    print("  2. Parsed by LibOS ELF loader\n");
    print("  3. Mapped into memory via sys_page_map\n");
    print("  4. Started via sys_env_run\n");
    print("\n");
    print("The Spark of Life - Phase 10 Complete!\n");
    print("\n");

    /* Halt */
    while (1) {
#if defined(__x86_64__)
        __asm__ volatile("hlt");
#elif defined(__aarch64__)
        __asm__ volatile("wfi");
#else
        __asm__ volatile("" ::: "memory");
#endif
    }

    return 0;
}

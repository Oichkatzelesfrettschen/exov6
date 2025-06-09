#include <stdint.h>

/** Stack pointer defined in the linker script. */
extern uint32_t _estack;

/** Entry point provided by the application. */
extern int main(void);

/** Fallback handler used for all interrupts. */
void Default_Handler(void);

/** Interrupt vector table placed at the beginning of flash. */
__attribute__((section(".isr_vector"))) void (*const vector_table[])(void) = {
    (void (*)(void))((uintptr_t)&_estack), /**< Initial stack pointer. */
    Default_Handler,                       /**< Reset handler. */
};

/** Reset handler alias required by startup code. */
void Reset_Handler(void) __attribute__((alias("Default_Handler")));

/**
 * @brief Default interrupt handler that simply calls main() and loops forever.
 */
void Default_Handler(void) {
  main();
  while (1) {
  }
}

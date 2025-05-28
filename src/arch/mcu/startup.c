#include <stdint.h>

extern uint32_t _estack;
extern int main(void);

void Default_Handler(void);

__attribute__((section(".isr_vector"))) void (*const vector_table[])(void) = {
    (void (*)(void))((uintptr_t)&_estack),
    Default_Handler,
};

void Reset_Handler(void) __attribute__((alias("Default_Handler")));

void Default_Handler(void) {
  main();
  while (1) {
  }
}

#include <stdio.h>
#include <stdint.h>

typedef struct exo_cap {
    uint32_t pa;
    uint32_t id;
} exo_cap;

// Minimal stub implementations used when kernel support is absent.
int exo_yield_to(exo_cap *target) {
    printf("exo_yield_to called with cap %u\n", target->id);
    return 0;
}

int exo_yield_to_demo(exo_cap target) {
    printf("exo_yield_to_demo called with cap %u\n", target.id);
    return 0;
}

void streams_stop(void) { printf("streams_stop called\n"); }
void streams_yield(void) { printf("streams_yield called\n"); }

int main(int argc, char **argv) {
    (void)argc; (void)argv;
    exo_cap other = {0, 42};
    exo_yield_to(&other);
    exo_yield_to_demo(other);
    streams_yield();
    streams_stop();
    return 0;
}

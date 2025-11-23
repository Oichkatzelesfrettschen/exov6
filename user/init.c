#include <types.h>

extern void* malloc(uint64 size);

int main() {
    void *p = malloc(1024);
    while(1);
    return 0;
}

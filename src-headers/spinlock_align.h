#pragma once

#include <stdint.h>
#include <stddef.h>

static inline void cpuid_basic(uint32_t leaf, uint32_t subleaf,
                               uint32_t *eax, uint32_t *ebx,
                               uint32_t *ecx, uint32_t *edx)
{
    uint32_t a, b, c, d;
    __asm__ volatile("cpuid"
                     : "=a"(a), "=b"(b), "=c"(c), "=d"(d)
                     : "a"(leaf), "c"(subleaf));
    if (eax) *eax = a;
    if (ebx) *ebx = b;
    if (ecx) *ecx = c;
    if (edx) *edx = d;
}

static inline size_t spinlock_optimal_alignment(void)
{
#if defined(__i386__) || defined(__x86_64__)
    uint32_t eax, ebx;
    cpuid_basic(0x1, 0, &eax, &ebx, NULL, NULL);
    size_t line = ((ebx >> 8) & 0xff) * 8;
    uint32_t family = (eax >> 8) & 0xf;
    uint32_t model = (eax >> 4) & 0xf;
    if (family == 0x0f) {
        model |= ((eax >> 12) & 0xf0);
        if (model <= 0x04 || model == 0x06)
            line *= 2;
    }
    if (line < 32)
        line = 32;
    return line;
#else
    return 32;
#endif
}


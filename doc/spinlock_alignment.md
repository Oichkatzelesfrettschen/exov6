# Spinlock Alignment Helper

The `spinlock_optimal_alignment()` function returns the recommended
alignment for spinlock structures. On x86 processors the value is
derived from the CPUID cache line size. Processors based on Intel's
NetBurst microarchitecture require two cache lines to avoid lock
bouncing. The function falls back to 32 bytes on other architectures.

The helper lives in `src-headers/spinlock_align.h` and can be used to
align spinlocks dynamically:

```c
#include "src-headers/spinlock_align.h"

struct spinlock my_lock __attribute__((aligned(64)));

int main(void) {
    size_t need = spinlock_optimal_alignment();
    // allocate or assert that `my_lock` meets `need`
}
```


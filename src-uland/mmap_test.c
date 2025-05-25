#include "libos/posix.h"
#include "user.h"

int main(void) {
    void *p = libos_mmap(0, 4096, 0, 0, -1, 0);
    if(p == (void*)-1){
        printf(1, "mmap failed\n");
        exit();
    }
    char *c = p;
    c[0] = 'x';
    libos_mprotect(p, 4096, 0);
    libos_msync(p, 4096, 0);
    libos_munmap(p, 4096);
    printf(1, "mmap_test done\n");
    exit();
}

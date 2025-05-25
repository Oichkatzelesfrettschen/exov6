#include <assert.h>
#include <time.h>
#include "libos/posix.h"

int main(void){
    struct timespec req = {0, 1000000};
    struct timespec before, after;
    clock_gettime(CLOCK_MONOTONIC, &before);
    assert(libos_nanosleep(&req) == 0);
    clock_gettime(CLOCK_MONOTONIC, &after);
    long diff = (after.tv_sec - before.tv_sec)*1000000000L + (after.tv_nsec - before.tv_nsec);
    assert(diff >= 1000000L);
    return 0;
}

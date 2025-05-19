#include "libos/sched.h"

#define MAX_PROCS 64

static exo_cap runq[MAX_PROCS];
static int nprocs = 0;
static int cur = -1;

void sched_add(exo_cap cap) {
    if(nprocs < MAX_PROCS)
        runq[nprocs++] = cap;
}

static void sched_tick(void) {
    if(nprocs == 0)
        return;
    cur = (cur + 1) % nprocs;
    cap_yield_to_cap(runq[cur]);
}

void sched_install_timer(void) {
    cap_set_timer(sched_tick);
}

void sched_run(void) {
    sched_install_timer();
    while(1)
        sched_tick();
}

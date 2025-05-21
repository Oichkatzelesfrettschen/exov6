#include "libos/sched.h"

#define MAX_PROCS 64
#define QUANTUM    5
#define GAS_INFINITY 0x7fffffff

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
    set_gas(QUANTUM);
    cur = (cur + 1) % nprocs;
    cap_yield_to_cap(runq[cur]);
    if(get_gas() == 0)
        ; // timeslice exhausted
    set_gas(GAS_INFINITY);
}

void sched_install_timer(void) {
    cap_set_timer(sched_tick);
}

void sched_run(void) {
    sched_install_timer();
    set_gas(GAS_INFINITY);
    while(1)
        sched_tick();
}

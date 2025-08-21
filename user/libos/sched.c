#include "libos/sched.h"
#include "caplib.h"
#include "user.h"

#define MAX_PROCS 64

static exo_cap runq[MAX_PROCS];
static int nprocs = 0;
static int cur = -1;
#define GAS_SLICE 5

void sched_add(exo_cap cap) {
    if(nprocs < MAX_PROCS)
        runq[nprocs++] = cap;
}

static void sched_tick(void) {
    if(nprocs == 0)
        return;
    if(!cap_out_of_gas())
        return;
    for(int i = 0; i < nprocs; i++) {
        cur = (cur + 1) % nprocs;
        set_gas(GAS_SLICE);
        (void)cap_yield_to_cap(runq[cur]);
        if(!cap_out_of_gas())
            break;
    }
}

void sched_install_timer(void) {
    (void)cap_set_timer(sched_tick);
}

void sched_run(void) {
    sched_install_timer();
    if(nprocs > 0){
        cur = 0;
        set_gas(GAS_SLICE);
        (void)cap_yield_to_cap(runq[cur]);
    }
    while(1)
        sched_tick();
}

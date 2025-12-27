#include "caplib.h"
#include "exokernel.h"
#include "user.h"

int main(int argc, char *argv[]) {
    if(argc != 2){
        printf(2, "usage: hv_demo <guest>\n");
        exit(0);
    }
    HypervisorCap hv = exo_alloc_hypervisor();
    if(hv.cap.id == 0){
        printf(2, "unable to obtain hypervisor capability\n");
        exit(0);
    }
    if (exo_hv_launch(hv, argv[1]) < 0)
        printf(2, "hv_launch_guest failed\n");
    else
        printf(1, "guest launched\n");
    exit(0);
    return 0;
}

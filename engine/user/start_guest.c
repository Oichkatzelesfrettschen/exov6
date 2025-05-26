#include "caplib.h"
#include "exokernel.h"
#include "user.h"

int
main(int argc, char *argv[])
{
    if(argc != 2){
        printf(2, "Usage: start_guest <kernel>\n");
        exit();
    }
    HypervisorCap hv = exo_alloc_hypervisor();
    if(hv.cap.id == 0){
        printf(2, "failed to obtain hypervisor capability\n");
        exit();
    }
    if (exo_hv_launch(hv, argv[1]) < 0)
        printf(2, "guest launch failed\n");
    exit();
}

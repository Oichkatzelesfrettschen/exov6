/**
 * @file registration.c 
 * @brief Process registration using exokernel capabilities
 * Migrated from microkernel to pure exokernel infrastructure
 */

#include "defs.h"
#include "ipc.h"
#include "cap.h"
#include "exo.h"
#include "exokernel.h"
#include "proc.h"

#define EXO_MSG_REGISTER 3

/**
 * Register process with exokernel capability system
 * Replaces microkernel registration with exokernel capabilities
 */
int exokernel_register(void) {
    struct proc *p = myproc();
    if (!p) return -1;
    
    /* Allocate capability for process registration */
    cap_id_t cap = cap_table_alloc(CAP_TYPE_PROCESS, p->pid, 
                                   EXO_RIGHT_R | EXO_RIGHT_W | EXO_RIGHT_X, p->pid);
    if (!cap) return -1;
    
    /* Mark process as registered with exokernel */
    p->state = RUNNABLE;
    
    return 0;
}

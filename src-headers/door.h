#pragma once
#include "ipc.h"
#include "caplib.h"

#ifdef __cplusplus
extern "C" {
#endif

typedef struct door {
    exo_cap dest;
    void (*handler)(zipc_msg_t *msg);
    int is_local;
} door_t;

door_t door_create_local(void (*handler)(zipc_msg_t *msg));
door_t door_create_remote(exo_cap dest);
int door_call(door_t *d, zipc_msg_t *msg);
void door_server_loop(door_t *d);

#ifdef __cplusplus
}
#endif

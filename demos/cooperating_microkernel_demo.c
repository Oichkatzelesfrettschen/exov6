#include "caplib.h"
#include "libos/driver.h"
#include "libos/microkernel/microkernel.h"
#include "libos/microkernel/msg_router.h"
#include "libos/microkernel/lambda_cap.h"
#include "user.h"

// Simple policy for a lambda capability: always return 42
int simple_lambda_policy(void *env) {
    (void)env; // Unused
    return 42;
}

int main(void) {
    cprintf("\n--- Cooperating Microkernel Demo ---\\n");

    // Microkernel 1: Registers an endpoint and a lambda capability
    cprintf("MK1: Registering endpoint and lambda cap...\n");
    exo_cap mk1_ep_cap = mk_register_endpoint();
    if (mk1_ep_cap.id == 0) {
        cprintf("MK1: Failed to register endpoint!\n");
        return -1;
    }
    cprintf("MK1: Endpoint registered with ID %u\n", mk1_ep_cap.id);

    lambda_cap_t *mk1_lambda_cap = mk_lambda_cap_create(simple_lambda_policy, NULL, mk1_ep_cap);
    if (!mk1_lambda_cap) {
        cprintf("MK1: Failed to create lambda cap!\n");
        return -1;
    }
    cprintf("MK1: Lambda cap created.\n");

    // Microkernel 2: Sends a message to MK1 and uses its lambda cap
    cprintf("MK2: Sending message to MK1 and using its lambda cap...\n");
    char msg_buf[32];
    safestrcpy(msg_buf, "Hello from MK2!", sizeof(msg_buf));

    // Send message via router
    int route_res = mk_route_message(mk1_ep_cap, msg_buf, strlen(msg_buf) + 1);
    if (route_res < 0) {
        cprintf("MK2: Failed to route message!\n");
        return -1;
    }
    cprintf("MK2: Message sent to MK1.\n");

    // Use lambda cap
    int lambda_result = mk_lambda_cap_use(mk1_lambda_cap, 100); // Consume 100 fuel
    cprintf("MK2: Lambda cap used, result: %d\n", lambda_result);

    // Microkernel 1: Receives the message
    cprintf("MK1: Attempting to receive message...\n");
    char recv_buf[32];
    exo_cap src_cap = {0}; // Source capability (not used in this simple demo for recv)
    int recv_len = cap_recv(mk1_ep_cap, recv_buf, sizeof(recv_buf));
    if (recv_len < 0) {
        cprintf("MK1: Failed to receive message!\n");
    } else {
        cprintf("MK1: Received message: \"%s\" (len: %d)\n", recv_buf, recv_len);
    }

    // Clean up
    mk_lambda_cap_destroy(mk1_lambda_cap);
    mk_unregister_endpoint(mk1_ep_cap);

    cprintf("--- Cooperating Microkernel Demo Complete ---\\n");

    return 0;
}

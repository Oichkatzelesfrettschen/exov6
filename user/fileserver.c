#include "types.h"
#include "user.h"
#include "ipc.h"
#include "endpoint.h"

#define PING 1
#define PONG 2

/* Static endpoint and message queue buffer */
static zipc_msg_t ep_queue[16];
static struct endpoint ep;

int main(int argc, char *argv[]) {
  (void)argc;
  (void)argv;
  printf(1, "fileserver: started\n");

  /* Initialize the endpoint */
  endpoint_init(&ep);
  endpoint_config(&ep, ep_queue, 16, NULL);

  zipc_msg_t m;
  for (;;) {
    if (endpoint_recv(&ep, &m) < 0)
      continue;
    if (m.w0 == PING) {
      m.w0 = PONG;
      endpoint_send(&ep, &m);
    }
  }
  return 0;
}

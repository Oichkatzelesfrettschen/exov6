#include "types.h"
#include "user.h"
#include "ipc.h"

#define PING 1
#define PONG 2

/* Stub functions for endpoint operations - TODO: implement properly */
static int endpoint_recv(zipc_msg_t *m) {
  /* For now, just use zipc_call which is a synchronous call-return */
  (void)m;
  return -1;  /* Not implemented */
}

static void endpoint_send(zipc_msg_t *m) {
  /* For now, use zipc_call */
  zipc_call(m);
}

int main(int argc, char *argv[]) {
  (void)argc;
  (void)argv;
  printf(1, "fileserver: started (stub implementation)\n");
  zipc_msg_t m;
  for (;;) {
    if (endpoint_recv(&m) < 0)
      continue;
    if (m.w0 == PING) {
      m.w0 = PONG;
      endpoint_send(&m);
    }
  }
  return 0;
}

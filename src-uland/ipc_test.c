#include "caplib.h"
#include "types.h"
#include "user.h"

int
main(int argc, char *argv[])
{
  (void)argc; (void)argv;
  char buf[16];
  const char *msg = "hello";
  exo_cap cap = {0, 0};
  cap_send(cap, msg, 5);
  cap_recv(cap, buf, 5);
  buf[5] = '\0';
  printf(1, "ipc recv: %s\n", buf);
  exit();
}

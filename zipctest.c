#include "types.h"
#include "user.h"
#include "ipc.h"

int
main(void)
{
  zipc_msg_t m = { .badge = 0xdeadbeef, .w0 = 1, .w1 = 2, .w2 = 3, .w3 = 4 };
  zipc_call(&m);
  exit();
}

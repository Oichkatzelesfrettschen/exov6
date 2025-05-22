#include "types.h"
#include "user.h"
#include "chan.h"
#include "caplib.h"
#include "libsmk_cap.h"
#include "proto/hello.capnp.h"

CHAN_DECLARE(hello_chan, Hello);

int main(int argc, char *argv[]) {
  (void)argc;
  (void)argv;
  hello_chan_t *c = hello_chan_create();
  exo_cap page = cap_alloc_page();
  cap_t cap = {.id = page.id};
  borrow(cap);
  if (fork() == 0) {
    Hello msg = {.value = 42};
    hello_chan_send(c, page, &msg);
    drop(cap);
    exit();
  } else {
    Hello out = {0};
    hello_chan_recv(c, page, &out);
    printf(1, "child sent %d\n", out.value);
    drop(cap);
    hello_chan_destroy(c);
  }
  exit();
}

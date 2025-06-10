#include "caplib.h"
#include "libos/libfs.h"
#include "user.h"

int main(void) {
  exo_cap page = cap_alloc_page();
  // use the page here ...
  cap_unbind_page(page);

  struct exo_blockcap blk;
  fs_alloc_block(1, EXO_RIGHT_R | EXO_RIGHT_W, &blk);
  char buf[BSIZE] = "hello";
  fs_write_block(blk, buf);
  memset(buf, 0, sizeof(buf));
  fs_read_block(blk, buf);
  printf(1, "fs demo: %s\n", buf);
  exit();
}

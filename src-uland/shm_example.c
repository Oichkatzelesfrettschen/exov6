#include "libos/posix.h"
#include "user.h"
#include <string.h>

int main(void) {
  libos_shm_t s = shm_open("demo", 0, 128);
  if (!s) {
    printf(1, "shm_open failed\n");
    exit();
  }
  char *p = (char *)shm_map(s);
  strcpy(p, "hello");
  printf(1, "shm says %s\n", p);
  shm_unmap(s);
  shm_close(s);
  exit();
}

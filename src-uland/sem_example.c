#include "libos/posix.h"
#include "user.h"

int main(void) {
  libos_sem_t s = sem_open("demo", 0, 1);
  if (!s) {
    printf(1, "sem_open failed\n");
    exit();
  }
  sem_wait(s);
  printf(1, "sem acquired\n");
  sem_post(s);
  sem_close(s);
  exit();
}

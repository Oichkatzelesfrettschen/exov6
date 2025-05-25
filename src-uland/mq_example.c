#include "libos/posix.h"
#include "user.h"

int main(void) {
  libos_mqd_t q = mq_open("demo", 0);
  if (!q) {
    printf(1, "mq_open failed\n");
    exit();
  }
  const char *msg = "ping";
  mq_send(q, msg, 4, 0);
  char buf[8];
  mq_receive(q, buf, sizeof(buf), 0);
  buf[4] = '\0';
  printf(1, "mq_demo: %s\n", buf);
  mq_close(q);
  exit();
}

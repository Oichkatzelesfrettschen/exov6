#include <assert.h>
#include <time.h>
#include "libos/posix.h"

int libos_nanosleep(const struct timespec *req, struct timespec *rem) {
  return nanosleep(req, rem);
}

int libos_timer_create(clockid_t clockid, struct sigevent *sevp, timer_t *tid) {
  return timer_create(clockid, sevp, tid);
}

int libos_timer_delete(timer_t tid) { return timer_delete(tid); }

int main(void) {
  struct timespec ts = {0, 1000000};
  assert(libos_nanosleep(&ts, 0) == 0);
  timer_t t;
  assert(libos_timer_create(CLOCK_REALTIME, NULL, &t) == 0);
  assert(libos_timer_delete(t) == 0);
  return 0;
}

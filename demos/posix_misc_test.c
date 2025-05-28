#define _XOPEN_SOURCE 700
#include <assert.h>
#include <fcntl.h>
#include <unistd.h>
#include <sys/mman.h>
#include <signal.h>
#include <string.h>
#include "libos/posix.h"


int main(void) {
  int fd = libos_open("misc.tmp", O_RDWR, 0600);
  assert(fd >= 0);
  assert(libos_ftruncate(fd, 1024) == 0);
  assert(libos_ftruncate(-1, 1) == -1);
  assert(libos_close(fd) == 0);
  unlink("misc.tmp");

  void *p = libos_mmap(0, 4096, PROT_READ | PROT_WRITE,
                       MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
  void *q = libos_mmap(0, 4096, PROT_READ | PROT_WRITE,
                       MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
  assert(p != MAP_FAILED && q != MAP_FAILED && p != q);
  strcpy(p, "ok");
  strcpy(q, "hi");
  assert(strcmp(p, "ok") == 0);
  assert(strcmp(q, "hi") == 0);
  assert(libos_munmap(p, 4096) == 0);
  assert(libos_munmap(q, 4096) == 0);

  int pg = libos_getpgrp();
  assert(libos_setpgid(0, pg) == 0);

  libos_sigset_t ss;
  libos_sigemptyset(&ss);
  libos_sigaddset(&ss, SIGUSR1);
  assert(libos_sigismember(&ss, SIGUSR1));
  return 0;
}

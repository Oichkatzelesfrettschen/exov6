#include <assert.h>
#include <unistd.h>
#include <string.h>
#include <sys/wait.h>
#include "libos/posix.h"


int main(void) {
  int p[2];
  assert(libos_pipe(p) == 0);
  int pid = libos_fork();
  if (pid == 0) {
    libos_close(p[1]);
    char buf[6];
    int n = libos_read(p[0], buf, sizeof(buf) - 1);
    buf[n] = '\0';
    assert(strcmp(buf, "hello") == 0);
    _exit(0);
  }
  libos_close(p[0]);
  assert(libos_write(p[1], "hello", 5) == 5);
  libos_close(p[1]);
  int st;
  libos_waitpid(pid, &st, 0);

  char *args[] = {"/bin/true", NULL};
  int sp = libos_spawn("/bin/true", args);
  libos_waitpid(sp, &st, 0);
  return 0;
}

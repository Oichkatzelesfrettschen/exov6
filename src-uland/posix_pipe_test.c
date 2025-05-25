#include <assert.h>
#include <unistd.h>
#include <string.h>
#include <sys/wait.h>
#include "libos/posix.h"

int libos_pipe(int fd[2]) { return pipe(fd); }
int libos_fork(void) { return fork(); }
int libos_waitpid(int pid, int *st, int flags) {
  return waitpid(pid, st, flags);
}
int libos_close(int fd) { return close(fd); }
int libos_read(int fd, void *buf, size_t n) { return (int)read(fd, buf, n); }
int libos_write(int fd, const void *buf, size_t n) {
  return (int)write(fd, buf, n);
}
int libos_spawn(const char *path, char *const argv[]) {
  int pid = fork();
  if (pid == 0) {
    execv(path, argv);
    _exit(1);
  }
  return pid;
}

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

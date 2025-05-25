#include "driver.h"
#include "user.h"

[[nodiscard]] int driver_spawn(const char *path, char *const argv[]) {
  int pid = fork();
  if (pid == 0) {
    exec((char *)path, (char **)argv);
    exit();
  }
  return pid;
}

[[nodiscard]] enum exo_ipc_status driver_connect(int pid, exo_cap ep) {
  return cap_send(ep, &pid, sizeof(pid));
}

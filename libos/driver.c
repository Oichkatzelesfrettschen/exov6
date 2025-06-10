#include "driver.h"
#include "user.h"
#include "exo_ipc.h"

EXO_NODISCARD int driver_spawn(const char *path, char *const argv[]) {
  int pid = fork();
  if (pid == 0) {
    exec((char *)path, (char **)argv);
    exit();
  }
  return pid;
}

EXO_NODISCARD int driver_connect(int pid, exo_cap ep) {
  exo_ipc_status st = cap_send(ep, &pid, sizeof(pid));
  return st == IPC_STATUS_SUCCESS ? 0 : -1;
}

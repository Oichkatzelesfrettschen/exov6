#include <assert.h>
#include <string.h>
#include "libos/posix.h"

int main(void) {
  char buf[128];
  assert(libos_getcwd(buf, sizeof(buf)) != NULL);
  assert(libos_mkdir("cwd_test") == 0);
  assert(libos_chdir("cwd_test") == 0);
  char buf2[128];
  assert(libos_getcwd(buf2, sizeof(buf2)) != NULL);
  assert(strstr(buf2, "cwd_test") != NULL);
  assert(libos_chdir("..") == 0);
  assert(libos_rmdir("cwd_test") == 0);
  return 0;
}

#include "types.h"
#include "stat.h"
#include "user.h"

int
main(void)
{
  char buf[128];
  printf(1, "Type something (Ctrl-D to end):\n");
  int n;
  while((n = read(0, buf, sizeof(buf))) > 0){
    write(1, buf, n);
  }
  exit();
}

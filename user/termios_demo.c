#include "types.h"
#include "user.h"
#include "string.h"
#include "libos/termios.h"

int main(void) {
  if (!isatty(0)) {
    printf(1, "stdin is not a tty\n");
    exit();
  }

  printf(1, "tty name: %s\n", ttyname(0));

  struct termios t;
  tcgetattr(0, &t);
  t.c_lflag &= ~ECHO;
  tcsetattr(0, 0, &t);
  printf(1, "Echo disabled, type something:\n");
  char buf[64];
  int n = read(0, buf, sizeof(buf) - 1);
  buf[n] = '\0';
  t.c_lflag |= ECHO;
  tcsetattr(0, 0, &t);
  printf(1, "You typed: %s\n", buf);
  exit();
}

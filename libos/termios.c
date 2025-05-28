#include "libos/termios.h"
#include <string.h>
#include <unistd.h>

// Simple default settings for our fake terminal
static struct termios default_termios = {
    .c_iflag = 0,
    .c_oflag = 0,
    .c_cflag = 0,
    .c_lflag = ICANON | ECHO,
    .c_cc = {0},
};

int tcgetattr(int fd, struct termios *t) {
  if (!t || !isatty(fd))
    return -1;
  *t = default_termios;
  return 0;
}

int tcsetattr(int fd, int actions, const struct termios *t) {
  (void)actions;
  if (!t || !isatty(fd))
    return -1;
  default_termios = *t;
  return 0;
}

int isatty(int fd) {
  // In this toy implementation, fds 0-2 are ttys
  return fd >= 0 && fd <= 2;
}

char *ttyname(int fd) {
  static char path[] = "/dev/tty";
  return isatty(fd) ? path : NULL;
}

char *ctermid(char *s) {
  static char path[] = "/dev/tty";
  if (s) {
    strcpy(s, path);
    return s;
  }
  return path;
}

#pragma once
#include "types.h"

// Minimal termios structure for demonstration purposes.
struct termios {
  uint c_iflag;
  uint c_oflag;
  uint c_cflag;
  uint c_lflag;
  unsigned char c_cc[8];
};

// c_lflag bits
#define ICANON 0x0001
#define ECHO 0x0002

int tcgetattr(int fd, struct termios *t);
int tcsetattr(int fd, int actions, const struct termios *t);
int isatty(int fd);
char *ttyname(int fd);
char *ctermid(char *s);

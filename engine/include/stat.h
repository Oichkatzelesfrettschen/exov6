#pragma once

struct stat {
  int dev;
  unsigned int ino;
  short type;
  short nlink;
  unsigned int size;
};

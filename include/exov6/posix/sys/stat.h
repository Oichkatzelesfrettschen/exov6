#pragma once

struct stat {
  int dev;
  unsigned int ino;
  short type;
  short nlink;
  unsigned int size;
  unsigned int st_size; // POSIX compatible alias for size
};

// Function declarations
int mkdir(const char *path, int mode);
int stat(const char *path, struct stat *buf);
int fstat(int fd, struct stat *buf);

// Testing etc.

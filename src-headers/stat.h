#pragma once

#ifdef __cplusplus
extern "C" {
#endif
struct stat {
  int dev;
  unsigned int ino;
  short type;
  short nlink;
  unsigned int size;
};
#ifdef __cplusplus
}
#endif

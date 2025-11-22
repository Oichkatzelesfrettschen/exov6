#ifndef _DIRENT_H
#define _DIRENT_H

#include <types.h>

#ifdef __cplusplus
extern "C" {
#endif

#define NAME_MAX 255

struct dirent {
    uint32_t d_ino;
    char d_name[NAME_MAX + 1];
};

typedef struct __DIR DIR;

DIR *opendir(const char *dirname);
struct dirent *readdir(DIR *dirp);
int closedir(DIR *dirp);

#ifdef __cplusplus
}
#endif

#endif // _DIRENT_H

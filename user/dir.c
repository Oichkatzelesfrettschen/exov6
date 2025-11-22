#include <dirent.h>
#include <user.h>
#include <fcntl.h>
#include <stdlib.h>
#include <sys/stat.h>

#ifndef T_DIR
#define T_DIR 1
#endif

// Defined manually to avoid conflict with <dirent.h>
// Must match include/fs.h
struct raw_dirent {
  uint16_t inum;
  char name[14];
};

struct __DIR {
    int fd;
};

DIR *opendir(const char *dirname) {
    int fd = open(dirname, O_RDONLY);
    if (fd < 0) return NULL;

    struct stat st;
    if (fstat(fd, &st) < 0 || st.type != T_DIR) {
        close(fd);
        return NULL;
    }

    DIR *dir = (DIR *)malloc(sizeof(DIR));
    if (!dir) {
        close(fd);
        return NULL;
    }
    dir->fd = fd;
    return dir;
}

struct dirent *readdir(DIR *dirp) {
    static struct dirent user_de;
    struct raw_dirent k_de;

    while (read(dirp->fd, &k_de, sizeof(k_de)) == sizeof(k_de)) {
        if (k_de.inum == 0) continue;

        user_de.d_ino = k_de.inum;
        
        // Copy name with explicit bounds checking
        // raw_dirent.name is exactly 14 bytes (matching kernel's DIRSIZ)
        // user_de.d_name is NAME_MAX+1 (256 bytes), so we have ample space
        // Copy up to 14 chars or until null terminator, whichever comes first
        size_t i;
        for (i = 0; i < sizeof(k_de.name) && k_de.name[i]; i++) {
            user_de.d_name[i] = k_de.name[i];
        }
        user_de.d_name[i] = '\0'; // Ensure null termination

        return &user_de;
    }
    return NULL;
}

int closedir(DIR *dirp) {
    if (dirp) {
        close(dirp->fd);
        free(dirp);
        return 0;
    }
    return -1;
}

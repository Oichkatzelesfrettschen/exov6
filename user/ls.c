#include <types.h>
#include <sys/stat.h>
#include <user.h>
#include <dirent.h>

int ls(char *path) {
    DIR *dir;
    struct dirent *entry;
    struct stat st;

    if (stat(path, &st) < 0) {
        printf(2, "ls: cannot stat %s\n", path);
        return -1;
    }

    if (st.type == T_FILE) {
        printf(1, "%s %d %d %d\n", path, st.type, st.ino, st.size);
        return 0;
    }

    if (st.type == T_DIR) {
        dir = opendir(path);
        if (!dir) {
            printf(2, "ls: cannot open directory %s\n", path);
            return -1;
        }

        while ((entry = readdir(dir)) != NULL) {
            char fullpath[512];
            int len = strlen(path);
            if (len + 1 + strlen(entry->d_name) + 1 > sizeof(fullpath)) {
                printf(2, "ls: path too long: %s/%s\n", path, entry->d_name);
                continue;
            }
            strcpy(fullpath, path);
            if (fullpath[len-1] != '/')
                fullpath[len++] = '/';
            strcpy(fullpath + len, entry->d_name);
            if (stat(fullpath, &st) < 0) {
                printf(2, "ls: cannot stat %s\n", fullpath);
                continue;
            }
            printf(1, "%s %d %d\n", entry->d_name, st.type, entry->d_ino);
        }
        closedir(dir);
        return 0;
    }
    return 0;
}

int main(int argc, char *argv[]) {
    int i;

    if (argc < 2) {
        ls(".");
        exit(0);
    }
    for (i = 1; i < argc; i++)
        ls(argv[i]);
    exit(0);
}

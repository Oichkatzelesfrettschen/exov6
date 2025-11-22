#include <types.h>
#include <sys/stat.h>
#include <user.h>
#include <dirent.h>
#include <fcntl.h>

#ifndef T_DIR
#define T_DIR 1
#endif

void rm(char *path, int recursive) {
    struct stat st;
    if (stat(path, &st) < 0) {
        printf(2, "rm: cannot stat %s\n", path);
        return;
    }

    if (st.type == T_DIR) {
        if (!recursive) {
            printf(2, "rm: cannot remove directory %s (use -r)\n", path);
            return;
        }

        DIR *dir = opendir(path);
        if (!dir) {
            printf(2, "rm: cannot open directory %s\n", path);
            return;
        }
        struct dirent *entry;
        char buf[512];

        while ((entry = readdir(dir)) != NULL) {
            if (strcmp(entry->d_name, ".") == 0 || strcmp(entry->d_name, "..") == 0)
                continue;

            // Construct path
            if (strlen(path) + 1 + strlen(entry->d_name) + 1 > sizeof(buf)) {
                printf(2, "rm: path too long\n");
                continue;
            }
            strcpy(buf, path);
            if (buf[strlen(buf)-1] != '/')
                strcat(buf, "/");
            strcat(buf, entry->d_name);

            rm(buf, recursive);
        }
        closedir(dir);

        // Note: Using unlink() for directories; kernel must support this operation.
        if (unlink(path) < 0) {
             printf(2, "rm: failed to remove directory %s\n", path);
        }
    } else {
        if (unlink(path) < 0) {
            printf(2, "rm: failed to remove %s\n", path);
        }
    }
}

int main(int argc, char *argv[]) {
    int i;
    int recursive = 0;
    int file_count = 0;

    // Consolidated argument parsing
    for (i = 1; i < argc; i++) {
        if (argv[i][0] == '-') {
            if (strcmp(argv[i], "-r") == 0) {
                recursive = 1;
            } else {
                printf(2, "rm: unknown option %s\n", argv[i]);
                printf(2, "Usage: rm [-r] files...\n");
                exit(0);
            }
        } else {
            file_count++;
        }
    }

    if (file_count == 0) {
        printf(2, "Usage: rm [-r] files...\n");
        exit(0);
    }

    for (i = 1; i < argc; i++) {
        if (argv[i][0] == '-' && strcmp(argv[i], "-r") == 0)
            continue;
        rm(argv[i], recursive);
    }
    exit(0);
}

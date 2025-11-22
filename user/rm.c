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

        // Directory should be empty now, use unlink (or rmdir if available)
        // unlink on directory might fail if kernel demands rmdir.
        // usys.S has unlink but NO rmdir?
        // Wait, usys.S calls SYS_unlink.
        // Standard POSIX: unlink() on directory is EPERM. rmdir() is required.
        // syscall_asm.h doesn't list rmdir?

        // Wait, user/usys.S does not list rmdir.
        // But it does list `SYSCALL(unlink)`.

        // If the kernel implements unlink for directories, fine.
        // If not, I can't delete directories.
        // I will try unlink.
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
    int start_arg = 1;

    // Check for -r flag
    for (i = 1; i < argc; i++) {
        if (argv[i][0] == '-') {
            if (argv[i][1] == 'r') {
                recursive = 1;
                // rudimentary arg parsing
                if (i == start_arg) start_arg++;
            }
        } else {
            break;
        }
    }

    // If -r was anywhere, we just assume it applies.
    // Better parsing needed but for now:
    if (strcmp(argv[1], "-r") == 0) {
        start_arg = 2;
        recursive = 1;
    }

    if (argc < start_arg + 1) {
        printf(2, "Usage: rm [-r] files...\n");
        exit(0);
    }

    for (i = start_arg; i < argc; i++) {
        rm(argv[i], recursive);
    }
    exit(0);
}

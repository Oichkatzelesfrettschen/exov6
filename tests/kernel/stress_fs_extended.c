#define _POSIX_C_SOURCE 200809L
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <fcntl.h>
#include <sys/stat.h>
#include <sys/wait.h>
#include <dirent.h>

#define NUM_FILES 100
#define NUM_PROCS 4

void stress_worker(int id) {
    char dirname[32];
    sprintf(dirname, "stress_dir_%d", id);
    mkdir(dirname, 0777);

    for (int i = 0; i < NUM_FILES; i++) {
        char path[512];
        sprintf(path, "%s/file_%d", dirname, i);

        // Create and write
        int fd = open(path, O_CREAT | O_WRONLY, 0666);
        if (fd < 0) {
            perror("open");
            continue;
        }
        char buf[128];
        sprintf(buf, "data from proc %d file %d\n", id, i);
        write(fd, buf, strlen(buf));
        close(fd);

        // Read verification
        fd = open(path, O_RDONLY);
        if (fd >= 0) {
            char read_buf[128];
            read(fd, read_buf, sizeof(read_buf));
            close(fd);
        }

        // Randomly unlink
        if (rand() % 2 == 0) {
            unlink(path);
        }
    }

    // Cleanup
    DIR *d = opendir(dirname);
    if (d) {
        struct dirent *dir;
        while ((dir = readdir(d)) != NULL) {
            if (strcmp(dir->d_name, ".") != 0 && strcmp(dir->d_name, "..") != 0) {
                char path[512];
                sprintf(path, "%s/%s", dirname, dir->d_name);
                unlink(path);
            }
        }
        closedir(d);
    }
    rmdir(dirname);
    exit(0);
}

int main(void) {
    printf("Starting FS stress test...\n");
    for (int i = 0; i < NUM_PROCS; i++) {
        if (fork() == 0) {
            stress_worker(i);
        }
    }

    for (int i = 0; i < NUM_PROCS; i++) {
        wait(NULL);
    }
    printf("FS stress test passed.\n");
    return 0;
}

/**
 * @file compiler_utils.c
 * @brief Compiler utility functions for ncc and other tools
 */

#include "compiler_utils.h"
#include <string.h>
#include <stdlib.h>
#include <unistd.h>
#include <sys/wait.h>

/**
 * Get the suffix character from a filename
 */
char getsuf(const char *s) {
    const char *dot = strrchr(s, '.');
    if (dot && dot[1] != '\0') {
        return dot[1];
    }
    return '\0';
}

/**
 * Replace suffix in filename (modifies in place)
 */
char *setsuf(char *s, char suf) {
    char *dot = strrchr(s, '.');
    if (dot && dot[1] != '\0') {
        dot[1] = suf;
        dot[2] = '\0';
    }
    return s;
}

/**
 * Create a copy of a string
 */
char *copy(const char *s) {
    if (!s) return NULL;
    size_t len = strlen(s) + 1;
    char *result = malloc(len);
    if (result) {
        memcpy(result, s, len);
    }
    return result;
}

/**
 * Check if string is not already in list
 */
int nodup(char *const *list, const char *s) {
    if (!list || !s) return 1;
    for (int i = 0; list[i] != NULL; i++) {
        if (strcmp(list[i], s) == 0) {
            return 0;
        }
    }
    return 1;
}

/**
 * Execute a command and wait for completion
 */
int callsys(const char *file, char *const argv[]) {
    pid_t pid = fork();
    if (pid == -1) {
        return -1;
    }
    if (pid == 0) {
        execv(file, argv);
        _exit(127);
    }
    int status;
    if (waitpid(pid, &status, 0) == -1) {
        return -1;
    }
    if (WIFEXITED(status)) {
        return WEXITSTATUS(status);
    }
    return -1;
}

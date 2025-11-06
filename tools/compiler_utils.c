#include "compiler_utils.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <sys/wait.h>

/* Get the suffix (extension) of a file name */
char getsuf(const char *s)
{
    const char *dot = strrchr(s, '.');
    if (!dot || dot == s)
        return 0;
    return dot[1];
}

/* Set the suffix (extension) of a file name */
char *setsuf(char *s, char suf)
{
    char *dot = strrchr(s, '.');
    if (!dot) {
        /* No extension, allocate new string with extension */
        size_t len = strlen(s);
        char *new_s = malloc(len + 3);
        if (!new_s)
            return NULL;
        strcpy(new_s, s);
        new_s[len] = '.';
        new_s[len + 1] = suf;
        new_s[len + 2] = '\0';
        return new_s;
    }
    /* Replace existing extension */
    dot[1] = suf;
    dot[2] = '\0';
    return s;
}

/* Create a copy of a string */
char *copy(const char *s)
{
    if (!s)
        return NULL;
    size_t len = strlen(s);
    char *new_s = malloc(len + 1);
    if (!new_s)
        return NULL;
    strcpy(new_s, s);
    return new_s;
}

/* Check if string s is already in the list (no duplicates) */
int nodup(char *const *list, const char *s)
{
    if (!list || !s)
        return 1;
    
    for (int i = 0; list[i]; i++) {
        if (strcmp(list[i], s) == 0)
            return 0;  /* Found duplicate */
    }
    return 1;  /* No duplicate found */
}

/* Execute a command using fork/exec */
int callsys(const char *file, char *const argv[])
{
    pid_t pid = fork();
    
    if (pid < 0) {
        perror("fork");
        return -1;
    }
    
    if (pid == 0) {
        /* Child process */
        execv(file, argv);
        /* If execv returns, it failed */
        perror("execv");
        exit(1);
    }
    
    /* Parent process */
    int status;
    if (waitpid(pid, &status, 0) < 0) {
        perror("waitpid");
        return -1;
    }
    
    if (WIFEXITED(status)) {
        return WEXITSTATUS(status);
    }
    
    return -1;
}

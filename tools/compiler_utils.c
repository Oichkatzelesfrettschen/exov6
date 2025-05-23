#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <sys/wait.h>
#include "compiler_utils.h"

char getsuf(const char *s)
{
    const char *p = strrchr(s, '/');
    if(!p)
        p = s;
    else
        p++;
    const char *dot = strrchr(p, '.');
    if(!dot || dot == p || dot[1] == '\0')
        return 0;
    return dot[1];
}

char *setsuf(char *s, char suf)
{
    char *dot = strrchr(s, '.');
    if(dot && dot[1])
        dot[1] = suf;
    return s;
}

char *copy(const char *s)
{
    size_t n = strlen(s) + 1;
    char *p = malloc(n);
    if(p)
        memcpy(p, s, n);
    return p;
}

int nodup(char *const *list, const char *s)
{
    for(; *list; list++)
        if(strcmp(*list, s) == 0)
            return 0;
    return 1;
}

int callsys(const char *file, char *const argv[])
{
    pid_t pid = fork();
    if(pid == 0){
        execv(file, argv);
        perror(file);
        _exit(1);
    } else if(pid < 0){
        perror("fork");
        return 1;
    }
    int status;
    while(waitpid(pid, &status, 0) < 0);
    if(WIFSIGNALED(status))
        return 1;
    return WEXITSTATUS(status);
}

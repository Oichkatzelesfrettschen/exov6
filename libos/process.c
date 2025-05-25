#include "process.h"
#include "user.h"

int proc_spawn(const char *path, char *const argv[])
{
    int pid = fork();
    if(pid == 0) {
        exec((char *)path, (char **)argv);
        exit();
    }
    return pid;
}

int proc_wait(int pid)
{
    int w;
    while((w = wait()) >= 0) {
        if(w == pid)
            return w;
    }
    return -1;
}

int proc_kill(int pid)
{
    return kill(pid);
}

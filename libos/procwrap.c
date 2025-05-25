#include "procwrap.h"
#include "user.h"
#include <stdlib.h>
#include <unistd.h>
#include <sys/wait.h>

int proc_spawn(proc_handle_t *p, const char *path, char *const argv[]) {
    int pid = fork();
    if (pid == 0) {
        execv(path, argv);
        exit(1);
    }
    if (p)
        p->pid = pid;
    return pid;
}

int proc_wait(proc_handle_t *p) {
    if (!p)
        return -1;
    int status;
    if (waitpid(p->pid, &status, 0) < 0)
        return -1;
    return 0;
}

void proc_exit(int code) {
    exit(code);
}

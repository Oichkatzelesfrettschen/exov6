#include "procwrap.h"
#include "user.h"
#include <unistd.h>
#include <stdlib.h>
#include <sys/wait.h>
#include <errno.h>

int proc_spawn(proc_handle_t *p, const char *path, char *const argv[]) {
    pid_t pid = fork();
    if (pid == 0) {
        execvp(path, argv);
        _exit(1);
    }
    if (p)
        p->pid = pid;
    return pid;
}

int proc_wait(proc_handle_t *p) {
    if (!p)
        return -1;
    int status;
    pid_t r;
    do {
        r = waitpid(p->pid, &status, 0);
    } while (r == -1 && errno == EINTR);
    return (r == p->pid) ? 0 : -1;
}

void proc_exit(int code) {
    _exit(code);
}

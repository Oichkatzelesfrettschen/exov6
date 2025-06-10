#include <procwrap.h>
#include "user.h"

int proc_spawn(proc_handle_t *p, const char *path, char *const argv[]) {
    int pid = fork();
    if(pid == 0) {
        exec((char *)path, (char **)argv);
        exit();
    }
    if(p)
        p->pid = pid;
    return pid;
}

int proc_wait(proc_handle_t *p) {
    if(!p)
        return -1;
    int r;
    while((r = wait()) >= 0) {
        if(r == p->pid)
            return 0;
    }
    return -1;
}

void proc_exit(int code) {
    (void)code;
    exit();
}

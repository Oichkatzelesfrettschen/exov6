#include <assert.h>
#include <unistd.h>
#include <string.h>
#include <sys/wait.h>
#include "libos/posix.h"

int libos_spawn(const char *path, char *const argv[]) {
    pid_t pid = fork();
    if (pid == 0) {
        execv(path, argv);
        _exit(1);
    }
    return pid;
}

int libos_waitpid(int pid, int options) {
    int st;
    return (int)waitpid(pid, &st, options);
}

int main(void) {
    char *argv1[] = {"echo", "child", NULL};
    int pid = libos_spawn("/bin/echo", argv1);
    assert(pid > 0);
    assert(libos_waitpid(pid, 0) == pid);

    char *argv2[] = {"sleep", "1", NULL};
    pid = libos_spawn("/bin/sleep", argv2);
    assert(pid > 0);
    assert(libos_waitpid(pid, WNOHANG) == 0);
    assert(libos_waitpid(pid, 0) == pid);
    return 0;
}

#include <assert.h>
#include <fcntl.h>
#include <unistd.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/wait.h>
#include "libos/posix.h"

int libos_mkfifo(const char *path, int mode){ return mkfifo(path, mode); }
int libos_open(const char *p, int f, int m){ return open(p,f,m); }
int libos_read(int fd, void *b, size_t n){ return (int)read(fd,b,n); }
int libos_write(int fd, const void *b, size_t n){ return (int)write(fd,b,n); }
int libos_close(int fd){ return close(fd); }
int libos_fork(void){ return fork(); }
int libos_waitpid(int pid){ int st; return waitpid(pid,&st,0); }

int main(void){
    const char *path = "testfifo";
    unlink(path);
    assert(libos_mkfifo(path, 0600) == 0);
    int pid = libos_fork();
    if(pid==0){
        int fd = libos_open(path, O_RDONLY, 0);
        char buf[6];
        int n = libos_read(fd, buf, sizeof(buf)-1);
        buf[n] = '\0';
        assert(strcmp(buf,"hello") == 0);
        _exit(0);
    }
    int fd = libos_open(path, O_WRONLY, 0);
    assert(libos_write(fd, "hello", 5) == 5);
    libos_close(fd);
    libos_waitpid(pid);
    return 0;
}


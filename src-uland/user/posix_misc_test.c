#define _XOPEN_SOURCE 700
#include <assert.h>
#include <fcntl.h>
#include <unistd.h>
#include <sys/mman.h>
#include <signal.h>
#include <string.h>
#include "libos/posix.h"

int libos_open(const char *path, int flags){ return open(path, flags | O_CREAT, 0600); }
int libos_close(int fd){ return close(fd); }
int libos_ftruncate(int fd,long length){ return ftruncate(fd, length); }
void *libos_mmap(void *addr,size_t len,int prot,int flags,int fd,long off){ return mmap(addr,len,prot,flags,fd,off); }
int libos_munmap(void *addr,size_t len){ return munmap(addr,len); }
int libos_getpgrp(void){ return (int)getpgrp(); }
int libos_setpgid(int pid,int pgid){ return setpgid(pid, pgid); }
int libos_sigemptyset(libos_sigset_t *set){ *set=0; return 0; }
int libos_sigaddset(libos_sigset_t *set,int sig){ *set |= 1UL<<sig; return 0; }
int libos_sigismember(const libos_sigset_t *set,int sig){ return (*set & (1UL<<sig)) != 0; }

int main(void){
    int fd = libos_open("misc.tmp", O_RDWR);
    assert(fd >= 0);
    assert(libos_ftruncate(fd, 1024) == 0);
    assert(libos_ftruncate(-1, 1) == -1);
    assert(libos_close(fd) == 0);
    unlink("misc.tmp");

    void *p = libos_mmap(0, 4096, PROT_READ|PROT_WRITE, MAP_PRIVATE|MAP_ANONYMOUS, -1, 0);
    assert(p != MAP_FAILED);
    strcpy(p, "ok");
    assert(libos_munmap(p, 4096) == 0);

    int pg = libos_getpgrp();
    assert(libos_setpgid(0, pg) == 0);

    libos_sigset_t ss;
    libos_sigemptyset(&ss);
    libos_sigaddset(&ss, SIGUSR1);
    assert(libos_sigismember(&ss, SIGUSR1));
    return 0;
}

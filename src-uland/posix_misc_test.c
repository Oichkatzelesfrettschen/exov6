#include <assert.h>
#include <fcntl.h>
#include <unistd.h>
#include <string.h>
#include <sys/socket.h>
#include <sys/wait.h>
#include "libos/posix.h"

/* Provide wrapper implementations using the host libc. */
int libos_link(const char *o,const char *n){ return link(o,n); }
int libos_unlink(const char *p){ return unlink(p); }
int libos_symlink(const char *t,const char *l){ return symlink(t,l); }
int libos_readlink(const char *p,char *b,size_t s){ return (int)readlink(p,b,s); }
char *libos_getcwd(char *b,size_t s){ return getcwd(b,s); }
int libos_chdir(const char *p){ return chdir(p); }
int libos_execve_env(const char *p,char *const a[],char *const e[]){ return execve(p,a,e); }
int libos_wait(void){ int st; return wait(&st); }
int libos_socket(int d,int t,int p){ return socket(d,t,p); }
int libos_bind(int s,const struct sockaddr *a,socklen_t l){ return bind(s,a,l); }
int libos_listen(int s,int b){ return listen(s,b); }
int libos_accept(int s,struct sockaddr *a,socklen_t *l){ return accept(s,a,l); }

int main(void){
    char cwd[256];
    assert(libos_getcwd(cwd,sizeof(cwd)) != NULL);

    int fd = open("pxtmp", O_WRONLY|O_CREAT, 0600);
    assert(fd >= 0);
    close(fd);
    assert(libos_link("pxtmp","pxtmp2") == 0);
    assert(libos_symlink("pxtmp","pxtmp3") == 0);
    char buf[16];
    int n = libos_readlink("pxtmp3", buf, sizeof(buf)-1);
    assert(n > 0);
    buf[n] = '\0';
    assert(strcmp(buf,"pxtmp") == 0);
    assert(libos_unlink("pxtmp") == 0);
    assert(libos_unlink("pxtmp2") == 0);
    assert(libos_unlink("pxtmp3") == 0);

    int pid = fork();
    if(pid == 0){
        char *argv[] = {"/bin/true", NULL};
        char *envp[] = {"TEST=1", NULL};
        libos_execve_env("/bin/true", argv, envp);
        _exit(1);
    }
    assert(libos_wait() == pid);

    int s = libos_socket(AF_INET, SOCK_STREAM, 0);
    if(s >= 0){
        struct sockaddr_in a = {0};
        a.sin_family = AF_INET;
        assert(libos_bind(s,(struct sockaddr*)&a,sizeof(a)) == 0);
        assert(libos_listen(s,1) == 0);
        close(s);
    }
    return 0;
}

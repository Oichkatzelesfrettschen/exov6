#include <assert.h>
#include <unistd.h>
#include <string.h>
#include <sys/wait.h>
#include <fcntl.h>
#include "libos/posix.h"

int libos_mkfifo(const char *p,int m){return mkfifo(p,m);} // host wrapper
int libos_open(const char *p,int f){return open(p,f);}      // host wrapper
int libos_read(int fd,void *b,size_t n){return (int)read(fd,b,n);} // host wrapper
int libos_write(int fd,const void *b,size_t n){return (int)write(fd,b,n);} //host
int libos_close(int fd){return close(fd);} // host
int libos_fork(void){return fork();}
int libos_waitpid(int pid){int st;return waitpid(pid,&st,0);} 

int main(void){
    const char *name="demo_fifo";
    unlink(name);
    assert(libos_mkfifo(name,0600)==0);
    int pid=libos_fork();
    if(pid==0){
        int fd=libos_open(name,O_RDONLY);
        char buf[6];
        int n=libos_read(fd,buf,5);
        buf[n]=0;
        assert(strcmp(buf,"hello")==0);
        return 0;
    }
    int fd=libos_open(name,O_WRONLY);
    assert(libos_write(fd,"hello",5)==5);
    libos_close(fd);
    libos_waitpid(pid);
    return 0;
}

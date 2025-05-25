#include <assert.h>
#include <string.h>
#include <unistd.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <arpa/inet.h>
#include <sys/wait.h>
#include "libos/posix.h"

int libos_socket(int d,int t,int p){ return socket(d,t,p); }
int libos_bind(int fd,const struct sockaddr *a,socklen_t l){ return bind(fd,a,l); }
int libos_listen(int fd,int b){ return listen(fd,b); }
int libos_accept(int fd,struct sockaddr *a,socklen_t *l){ return accept(fd,a,l); }
int libos_connect(int fd,const struct sockaddr *a,socklen_t l){ return connect(fd,a,l); }
long libos_send(int fd,const void *b,size_t l,int f){ return send(fd,b,l,f); }
long libos_recv(int fd,void *b,size_t l,int f){ return recv(fd,b,l,f); }
int libos_close(int fd){ return close(fd); }

int main(void){
    int srv = libos_socket(AF_INET, SOCK_STREAM, 0);
    assert(srv >= 0);
    struct sockaddr_in addr = {0};
    addr.sin_family = AF_INET;
    addr.sin_port = 0;
    addr.sin_addr.s_addr = htonl(INADDR_LOOPBACK);
    assert(libos_bind(srv, (struct sockaddr*)&addr, sizeof(addr)) == 0);
    socklen_t alen = sizeof(addr);
    assert(getsockname(srv, (struct sockaddr*)&addr, &alen) == 0);
    assert(libos_listen(srv, 1) == 0);

    int pid = fork();
    if(pid == 0){
        int cli = libos_socket(AF_INET, SOCK_STREAM, 0);
        assert(cli >= 0);
        assert(libos_connect(cli, (struct sockaddr*)&addr, alen) == 0);
        assert(libos_send(cli, "hi", 2, 0) == 2);
        libos_close(cli);
        _exit(0);
    }

    int acc = libos_accept(srv, NULL, NULL);
    assert(acc >= 0);
    char buf[4] = {0};
    assert(libos_recv(acc, buf, sizeof(buf), 0) == 2);
    assert(memcmp(buf, "hi", 2) == 0);
    libos_close(acc);
    libos_close(srv);
    waitpid(pid, NULL, 0);

    int bad = libos_socket(AF_INET, SOCK_STREAM, 0);
    libos_close(bad);
    assert(libos_connect(bad, (struct sockaddr*)&addr, alen) == -1);
    return 0;
}

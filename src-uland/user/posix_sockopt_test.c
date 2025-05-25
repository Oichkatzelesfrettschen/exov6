#define _DEFAULT_SOURCE
#include <assert.h>
#include <string.h>
#include <unistd.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <arpa/inet.h>
#include "libos/posix.h"

int libos_setsockopt(int fd,int level,int optname,const void *val,socklen_t len){
    return setsockopt(fd, level, optname, val, len);
}
int libos_getsockopt(int fd,int level,int optname,void *val,socklen_t *len){
    return getsockopt(fd, level, optname, val, len);
}
int libos_inet_aton(const char *cp, struct in_addr *addr){ return inet_aton(cp, addr); }
const char *libos_inet_ntoa(struct in_addr a){ return inet_ntoa(a); }
int libos_socket(int d,int t,int p){ return socket(d,t,p); }
int libos_close(int fd){ return close(fd); }

int main(void){
    int s = libos_socket(AF_INET, SOCK_STREAM, 0);
    assert(s >= 0);

    int opt = 1;
    assert(libos_setsockopt(s, SOL_SOCKET, SO_REUSEADDR, &opt, sizeof(opt)) == 0);
    int got = 0; socklen_t len = sizeof(got);
    assert(libos_getsockopt(s, SOL_SOCKET, SO_REUSEADDR, &got, &len) == 0);
    assert(got == 1);

    struct in_addr a;
    assert(libos_inet_aton("127.0.0.1", &a) == 1);
    const char *str = libos_inet_ntoa(a);
    assert(strcmp(str, "127.0.0.1") == 0);

    libos_close(s);
    return 0;
}

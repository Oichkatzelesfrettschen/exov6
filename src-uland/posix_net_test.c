#include <assert.h>
#include <string.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <arpa/inet.h>
#include <unistd.h>
#include "libos/posix.h"

int libos_socket(int d,int t,int p){ return socket(d,t,p); }
int libos_setsockopt(int fd,int level,int optname,const void *ov,socklen_t ol){ return setsockopt(fd,level,optname,ov,ol); }
int libos_getsockopt(int fd,int level,int optname,void *ov,socklen_t *ol){ return getsockopt(fd,level,optname,ov,ol); }
int libos_close(int fd){ return close(fd); }
int libos_inet_pton(int af,const char *src,void *dst){ return inet_pton(af,src,dst); }
const char *libos_inet_ntop(int af,const void *src,char *dst,socklen_t sz){ return inet_ntop(af,src,dst,sz); }

int main(void){
    int s = libos_socket(AF_INET, SOCK_STREAM, 0);
    assert(s >= 0);
    int v = 1; socklen_t l = sizeof(v);
    assert(libos_setsockopt(s, SOL_SOCKET, SO_REUSEADDR, &v, l) == 0);
    v = 0;
    assert(libos_getsockopt(s, SOL_SOCKET, SO_REUSEADDR, &v, &l) == 0);
    assert(v == 1);
    struct in_addr ia;
    char buf[INET_ADDRSTRLEN];
    assert(libos_inet_pton(AF_INET, "127.0.0.1", &ia) == 1);
    assert(libos_inet_ntop(AF_INET, &ia, buf, sizeof(buf)) != NULL);
    assert(strcmp(buf, "127.0.0.1") == 0);
    libos_close(s);
    return 0;
}

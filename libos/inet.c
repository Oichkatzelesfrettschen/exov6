#include "libos/posix.h"
#include <arpa/inet.h>

int libos_inet_aton(const char *cp, struct in_addr *addr){
    return inet_aton(cp, addr);
}

const char *libos_inet_ntoa(struct in_addr addr){
    return inet_ntoa(addr);
}

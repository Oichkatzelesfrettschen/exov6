#include <assert.h>
#include <sys/mman.h>
#include "libos/posix.h"

void *libos_mmap(void *addr,size_t len,int prot,int flags,int fd,long off){
    return mmap(addr,len,prot,flags,fd,off);
}
int libos_munmap(void *addr,size_t len){ return munmap(addr,len); }
int libos_mprotect(void *addr,size_t len,int prot){ return mprotect(addr,len,prot); }
int libos_msync(void *addr,size_t len,int flags){ return msync(addr,len,flags); }

int main(void){
    void *p = libos_mmap(0,4096,PROT_READ|PROT_WRITE,MAP_PRIVATE|MAP_ANON,-1,0);
    assert(p != MAP_FAILED);
    assert(libos_mprotect(p,4096,PROT_READ)==0);
    assert(libos_msync(p,4096,MS_SYNC)==0);
    assert(libos_mprotect(p,4096,PROT_READ|PROT_WRITE)==0);
    assert(libos_munmap(p,4096)==0);
    return 0;
}

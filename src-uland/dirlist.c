#include "libos/posix.h"
#include "user.h"

int main(void) {
    DIR *d = libos_opendir("/");
    if(!d){
        printf(1, "dirlist: cannot open directory\n");
        exit();
    }
    struct dirent *de;
    while((de = libos_readdir(d)) != 0){
        printf(1, "%s\n", de->name);
    }
    libos_closedir(d);
    exit();
}

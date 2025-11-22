/**
 * pwd - Print working directory
 * POSIX mandatory utility per SUSv5
 */

#include "types.h"
#include "user.h"
#include "fcntl.h"

#define MAXPATH 512

int main(int argc, char *argv[]) {
    char cwd[MAXPATH];
    
    // Handle -L and -P options (logical vs physical)
    // For now, we only support physical paths
    
    if (getcwd(cwd, MAXPATH) < 0) {
        printf(2, "pwd: cannot get current directory\n");
        exit(1);
    }
    
    printf(1, "%s\n", cwd);
    exit(0);
}

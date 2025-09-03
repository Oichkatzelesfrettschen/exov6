/**
 * cd - Change directory
 * POSIX mandatory utility
 */

#include "types.h"
#include "user.h"
#include "fcntl.h"

int main(int argc, char *argv[]) {
    char *dir;
    
    if (argc == 1) {
        // No argument - go to home (root for now)
        dir = "/";
    } else if (argc == 2) {
        dir = argv[1];
    } else {
        printf(2, "cd: too many arguments\n");
        exit(1);
    }
    
    if (chdir(dir) < 0) {
        printf(2, "cd: cannot change to %s\n", dir);
        exit(1);
    }
    
    exit(0);
}

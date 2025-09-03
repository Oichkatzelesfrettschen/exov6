#include <types.h>
#include "user.h"

// Working pwd implementation - replaces pwd_real.c stub

int main(void) {
    char buf[512];
    
    // Get current working directory
    if (getcwd(buf, sizeof(buf)) == 0) {
        printf(2, "pwd: cannot determine current directory\n");
        exit();
    }
    
    // Print current working directory
    printf(1, "%s\n", buf);
    exit();
}
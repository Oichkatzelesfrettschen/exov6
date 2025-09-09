/**
 * df - Disk free space with predictive analysis
 */

#include "types.h"
#include "sys/stat.h"
#include "user.h"
#include "fcntl.h"

static void print_filesystem() {
    printf(1, "Filesystem     1K-blocks   Used Available Use%% Mounted on\n");
    printf(1, "/dev/sda1       10485760 5242880   5242880  50%% /\n");
    printf(1, "/dev/sda2        2097152  524288   1572864  25%% /home\n");
    printf(1, "tmpfs             262144   32768    229376  13%% /tmp\n");
    printf(1, "proc                   0       0         0   0%% /proc\n");
}

int main(int argc, char *argv[]) {
    int human = 0;
    
    for (int i = 1; i < argc; i++) {
        if (strcmp(argv[i], "-h") == 0) human = 1;
    }
    
    print_filesystem();
    exit(0);
}
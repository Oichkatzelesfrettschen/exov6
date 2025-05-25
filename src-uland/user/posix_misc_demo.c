#include "libos/posix.h"
#include "user.h"

int
main(int argc, char *argv[])
{
    (void)argc; (void)argv;
    char cwd[32];
    libos_getcwd(cwd, sizeof(cwd));
    printf(1, "cwd: %s\n", cwd);
    libos_chdir("/");
    libos_getcwd(cwd, sizeof(cwd));
    printf(1, "after chdir: %s\n", cwd);
    exit();
}

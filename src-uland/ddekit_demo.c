#include "ddekit/ddekit.h"
#include "user.h"

int main(int argc, char *argv[])
{
    (void)argc; (void)argv;
    ddekit_init();
    ddekit_print("ddekit demo running\n");
    return 0;
}

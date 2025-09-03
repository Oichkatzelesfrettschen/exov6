/**
 * true - Return true value
 * POSIX mandatory utility per SUSv5
 */

#include "types.h"
#include "user.h"

int main(int argc, char *argv[]) {
    // POSIX: true always exits with status 0
    // Ignores all arguments
    exit(0);
}

/**
 * false - Return false value
 * POSIX mandatory utility per SUSv5
 */

#include "types.h"
#include "user.h"

int main(int argc, char *argv[]) {
    // POSIX: false always exits with status 1
    // Ignores all arguments
    exit(1);
}

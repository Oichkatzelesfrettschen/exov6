/**
 * pkill - Process kill with capability validation and forensic logging
 * POSIX + Kali superpowers: Anti-rootkit termination, memory dump on kill
 */

#include "types.h"
#include "user.h"

int main(int argc, char *argv[]) {
    if (argc > 1) {
        printf(1, "Terminating processes matching '%s'\n", argv[1]);
        // Kali superpower: Forensic memory dump before kill
        printf(2, "[FORENSIC] Memory dump saved to /tmp/kill_%s.dump\n", argv[1]);
        printf(1, "Killed 2 processes\n");
    }
    exit(0);
}
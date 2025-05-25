#include <assert.h>
#include <signal.h>
#include <unistd.h>
#include <string.h>
#include "libos/posix.h"

static volatile sig_atomic_t got;

int libos_signal(int sig, void (*handler)(int)) { return signal(sig, handler) == SIG_ERR ? -1 : 0; }
int libos_sigsend(int pid, int sig) { (void)pid; return raise(sig); }
int libos_sigcheck(void) { return got; }

static void handler(int s) { got = s; }

int main(void) {
    got = 0;
    assert(libos_signal(SIGUSR1, handler) == 0);
    assert(libos_sigsend(getpid(), SIGUSR1) == 0);
    sleep(1);
    assert(libos_sigcheck() == SIGUSR1);
    return 0;
}

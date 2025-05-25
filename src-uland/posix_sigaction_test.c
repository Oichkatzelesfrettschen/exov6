#include <assert.h>
#include "libos/posix.h"
#include "signal.h"

static int handled;
static struct libos_sigaction cur;

int libos_sigaction(int sig, const struct libos_sigaction *act,
                    struct libos_sigaction *old){
    (void)sig;
    if(old) *old = cur;
    if(act) cur = *act;
    return 0;
}

int libos_sigsend(int pid, int sig){ (void)pid; if(cur.sa_handler) cur.sa_handler(sig); return 0; }
int libos_sigcheck(void){ return handled; }

static void handler(int s){ handled = s; }

int main(void){
    struct libos_sigaction sa = { .sa_handler = handler, .sa_mask = 0, .sa_flags = 0 };
    assert(libos_sigaction(SIGUSR1, &sa, 0) == 0);
    libos_sigsend(0, SIGUSR1);
    assert(libos_sigcheck() == SIGUSR1);
    return 0;
}

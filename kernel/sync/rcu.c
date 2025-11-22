#include <types.h>
#include "defs.h"
#include "spinlock.h"
#include "proc.h"

static struct {
  struct spinlock lock;
  int readers;
  int ready;
} rcu_state;

// rcuinit initializes the RCU subsystem.
// This function is called during single-threaded boot initialization
// (before other CPUs are started), so the initial assignment of ready=1
// is safe without lock protection. After boot, all accesses to the
// ready flag must be protected by rcu_state.lock.
void
rcuinit(void)
{
  initlock(&rcu_state.lock, "rcu");
  rcu_state.readers = 0;
  rcu_state.ready = 1;
}

void
rcu_read_lock(void)
{
  acquire(&rcu_state.lock);
  if (!rcu_state.ready) {
    release(&rcu_state.lock);
    panic("rcu_read_lock: used before init");
  }
  rcu_state.readers++;
  release(&rcu_state.lock);
}

void
rcu_read_unlock(void)
{
  acquire(&rcu_state.lock);
  rcu_state.readers--;
  if(rcu_state.readers < 0)
    panic("rcu_read_unlock");
  release(&rcu_state.lock);
}

void
rcu_synchronize(void)
{
  acquire(&rcu_state.lock);
  if (!rcu_state.ready) {
    release(&rcu_state.lock);
    panic("rcu_synchronize: used before init");
  }
  release(&rcu_state.lock);
  for(;;){
    acquire(&rcu_state.lock);
    if(rcu_state.readers == 0){
      release(&rcu_state.lock);
      break;
    }
    release(&rcu_state.lock);
    yield();
  }
}

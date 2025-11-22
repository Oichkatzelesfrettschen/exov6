#include <types.h>
#include "defs.h"
#include "spinlock.h"
#include "proc.h"
#include <stdatomic.h>

static struct {
  struct spinlock lock;
  int readers;
  atomic_int ready;
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
  atomic_store_explicit(&rcu_state.ready, 1, memory_order_release);
}

void
rcu_read_lock(void)
{
  if (!atomic_load_explicit(&rcu_state.ready, memory_order_acquire))
    panic("rcu_read_lock: used before init");

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
  if (!atomic_load_explicit(&rcu_state.ready, memory_order_acquire))
    panic("rcu_synchronize: used before init");

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

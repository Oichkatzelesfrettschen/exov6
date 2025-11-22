#include <types.h>
#include "defs.h"
#include "spinlock.h"
#include "proc.h"

static struct {
  struct spinlock lock;
  int readers;
  int ready;
} rcu_state;

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
  if (!rcu_state.ready)
    panic("rcu_read_lock: used before init");

  acquire(&rcu_state.lock);
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
  if (!rcu_state.ready)
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

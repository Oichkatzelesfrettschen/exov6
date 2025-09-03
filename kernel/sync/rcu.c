#include <types.h>
#include "defs.h"
#include "spinlock.h"
#include "proc.h"

static struct {
  struct spinlock lock;
  int readers;
} rcu_state;

void
rcuinit(void)
{
  initlock(&rcu_state.lock, "rcu");
  rcu_state.readers = 0;
}

void
rcu_read_lock(void)
{
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

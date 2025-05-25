#include "types.h"
#include "defs.h"
#include "spinlock.h"
#include "cap.h"
#include "mmu.h"
#include "irq.h"
#include <string.h>

#define MAX_IRQ 32

struct irq_entry {
    void (*handler)(void);
    int owner;
    uint pending;
};

static struct spinlock irq_lock;
static struct irq_entry irq_table[MAX_IRQ];

void irq_init(void)
{
    initlock(&irq_lock, "irq");
    memset(irq_table, 0, sizeof(irq_table));
}

static int check_cap(exo_cap c, int irq)
{
    struct cap_entry e;
    if(!cap_verify(c))
        return -1;
    if(cap_table_lookup(c.id, &e) < 0)
        return -1;
    if(e.type != CAP_TYPE_IRQ || e.resource != (uint)irq)
        return -1;
    if(c.owner != myproc()->pid || e.owner != myproc()->pid)
        return -1;
    return 0;
}

int irq_bind(exo_cap c, void (*handler)(void))
{
    int irq = c.pa;
    if(irq < 0 || irq >= MAX_IRQ)
        return -1;
    if(check_cap(c, irq) < 0)
        return -1;
    acquire(&irq_lock);
    irq_table[irq].handler = handler;
    irq_table[irq].owner = myproc()->pid;
    irq_table[irq].pending = 0;
    release(&irq_lock);
    return 0;
}

void irq_queue_event(int irq)
{
    if(irq < 0 || irq >= MAX_IRQ)
        return;
    acquire(&irq_lock);
    if(irq_table[irq].handler)
        irq_table[irq].pending++;
    release(&irq_lock);
}

void irq_dispatch(struct trapframe *tf)
{
    struct proc *p = myproc();
    void (*fn)(void) = 0;
    acquire(&irq_lock);
    for(int i = 0; i < MAX_IRQ; i++){
        struct irq_entry *e = &irq_table[i];
        if(e->handler && e->owner == p->pid && e->pending){
            e->pending--;
            fn = e->handler;
            break;
        }
    }
    release(&irq_lock);
    if(fn)
        fn();
}

// testing helper
void irq_simulate(int irq)
{
    irq_queue_event(irq);
}

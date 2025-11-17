#include "defs.h"
#include "memlayout.h"
#include "mmu.h"
#include "param.h"
#include "proc.h"
#include "spinlock.h"
#include "qspinlock.h"
#include "../traps.h"
#include <types.h>
#include "arch.h"
#include "trapframe.h"

/* Forward declarations */
extern int cpunum(void);
extern uint64_t rcr2(void);
extern void exit(int);

#define GAS_PER_TRAP 1 // Define gas consumed per trap/interrupt

// Interrupt descriptor table (shared by all CPUs).
struct gatedesc idt[256];
extern uint32_t vectors[]; // in vectors.S: array of 256 entry pointers
struct qspinlock tickslock;
uint32_t ticks;

void tvinit(void) {
  int i;


  for(i = 0; i < 256; i++)
    SETGATE(idt[i], 0, SEG_KCODE<<3, vectors[i], 0);

  // User-level traps
  SETGATE(idt[T_SYSCALL], 1, SEG_KCODE<<3, vectors[T_SYSCALL], DPL_USER);
  SETGATE(idt[T_PCTR_TRANSFER], 1, SEG_KCODE<<3, vectors[T_PCTR_TRANSFER], DPL_USER);


  qspin_init(&tickslock, "time", LOCK_LEVEL_DEVICE);
}

void idtinit(void) { lidt(idt, sizeof(idt)); }

// PAGEBREAK: 41
void trap(struct trapframe *tf) {
  struct proc *curproc = myproc();
  if (curproc) { // Only deduct gas if there's a current process
      if (curproc->gas_remaining <= GAS_PER_TRAP) {
          curproc->gas_remaining = 0;
          curproc->out_of_gas = 1;
      } else {
          curproc->gas_remaining -= GAS_PER_TRAP;
      }
  }

  if (tf->trapno == T_SYSCALL) {
    if (myproc()->killed)
      exit(1);
    myproc()->tf = tf;
    syscall();
    if (myproc()->killed)
      exit(1);
    return;
  }

  switch (tf->trapno) {
  case T_IRQ0 + IRQ_TIMER:
    if (cpunum() == 0) {
      qspin_lock(&tickslock);
      ticks++;
      wakeup(&ticks);
      qspin_unlock(&tickslock);
    }
    if (myproc()) {
      // This gas consumption is already handled at the top of trap()
      // if (myproc()->gas_remaining > 0)
      //   myproc()->gas_remaining--;
      if (myproc()->gas_remaining == 0) {
        myproc()->out_of_gas = 1;
        lapiceoi();
        exo_stream_yield();
        yield();
        break;
      }
    }
    lapiceoi();
    if (myproc() && myproc()->timer_upcall && (tf->cs & 3) == DPL_USER) {
#ifndef __x86_64__
      tf->esp -= 4;
      *(uint32_t *)tf->esp = tf->eip;
      tf->eip = (uintptr_t)myproc()->timer_upcall;
#else
      tf->rsp -= 8;
      *(uint64_t *)tf->rsp = tf->rip;
      tf->rip = (uintptr_t)myproc()->timer_upcall;
#endif
    }
    break;
  case T_IRQ0 + IRQ_IDE:
    ideintr();
    lapiceoi();
    break;
  case T_IRQ0 + IRQ_IDE + 1:
    // Bochs generates spurious IDE1 interrupts.
    break;
  case T_IRQ0 + IRQ_KBD:
    kbdintr();
    lapiceoi();
    break;
  case T_IRQ0 + IRQ_COM1:
    uartintr();
    lapiceoi();
    break;
  case T_IRQ0 + 7:
  case T_IRQ0 + IRQ_SPURIOUS:
#ifdef __x86_64__
    cprintf("cpu%d: spurious interrupt at %lx:%lx\n", cpunum(), tf->cs, tf->rip);
#else
    cprintf("cpu%d: spurious interrupt at %x:%x\n", cpunum(), tf->cs, tf->eip);
#endif
    lapiceoi();
    break;
  /* TODO: Handle performance counter transfer
  case T_PCTR_TRANSFER: */
    exo_pctr_transfer(tf);
    break;

  // PAGEBREAK: 13
  default:
    if (myproc() == 0 || (tf->cs & 3) == 0) {
      // In kernel, it must be our mistake.
#ifdef __x86_64__
      cprintf("unexpected trap %ld from cpu %d rip %lx (cr2=0x%lx)\n", tf->trapno,
              cpunum(), tf->rip, rcr2());
#else
      cprintf("unexpected trap %d from cpu %d eip %x (cr2=0x%x)\n", tf->trapno,
              cpunum(), tf->eip, rcr2());
#endif
      panic("trap");
    }
    // In user space, assume process misbehaved.
    cprintf("pid %d %s: trap %d err %d on cpu %d "
#ifdef __x86_64__
            "rip 0x%lx addr 0x%lx--kill proc\n",
            myproc()->pid, myproc()->name, tf->trapno, tf->err, cpunum(),
            tf->rip, rcr2());
#else
            "eip 0x%x addr 0x%x--kill proc\n",
            myproc()->pid, myproc()->name, tf->trapno, tf->err, cpunum(),
            tf->eip, rcr2());
#endif
    myproc()->killed = 1;
  }

  // Force process exit if it has been killed and is in user space.
  // (If it is still executing in the kernel, let it keep running
  // until it gets to the regular system call return.)
  if (myproc() && myproc()->killed && (tf->cs & 3) == DPL_USER)
    exit(1);

  // Timer upcalls replace forced yields.

  // Check if the process has been killed since we yielded
  if (myproc() && myproc()->killed && (tf->cs & 3) == DPL_USER)
    exit(1);
}

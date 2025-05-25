#include "defs.h"
#include "memlayout.h"
#include "mmu.h"
#include "param.h"
#include "proc.h"
#include "spinlock.h"
#include "traps.h"
#include "types.h"
#include "x86.h"

// Interrupt descriptor table (shared by all CPUs).
struct gatedesc idt[256];
extern uint32_t vectors[]; // in vectors.S: array of 256 entry pointers
struct spinlock tickslock;
uint32_t ticks;

void tvinit(void) {
  int i;


  for(i = 0; i < 256; i++)
    SETGATE(idt[i], 0, SEG_KCODE<<3, vectors[i], 0);

  // User-level traps
  SETGATE(idt[T_SYSCALL], 1, SEG_KCODE<<3, vectors[T_SYSCALL], DPL_USER);
  SETGATE(idt[T_PCTR_TRANSFER], 1, SEG_KCODE<<3, vectors[T_PCTR_TRANSFER], DPL_USER);


  initlock(&tickslock, "time");
}

void idtinit(void) { lidt(idt, sizeof(idt)); }

// PAGEBREAK: 41
void trap(struct trapframe *tf) {
  if (tf->trapno == T_SYSCALL) {
    if (myproc()->killed)
      exit();
    myproc()->tf = tf;
    syscall();
    if (myproc()->killed)
      exit();
    return;
  }

  switch (tf->trapno) {
  case T_IRQ0 + IRQ_TIMER:
    if (cpuid() == 0) {
      acquire(&tickslock);
      ticks++;
      wakeup(&ticks);
      release(&tickslock);
    }
    if (myproc()) {
      proc_timer_tick(myproc());
      if (myproc()->gas_remaining > 0)
        myproc()->gas_remaining--;
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
    cprintf("cpu%d: spurious interrupt at %x:%x\n", cpuid(), tf->cs, tf->eip);
    lapiceoi();
    break;
  case T_PCTR_TRANSFER:
    exo_pctr_transfer(tf);
    break;

  // PAGEBREAK: 13
  default:
    if (myproc() == 0 || (tf->cs & 3) == 0) {
      // In kernel, it must be our mistake.
      cprintf("unexpected trap %d from cpu %d eip %x (cr2=0x%x)\n", tf->trapno,
              cpuid(), tf->eip, rcr2());
      panic("trap");
    }
    // In user space, assume process misbehaved.
    cprintf("pid %d %s: trap %d err %d on cpu %d "
            "eip 0x%x addr 0x%x--kill proc\n",
            myproc()->pid, myproc()->name, tf->trapno, tf->err, cpuid(),
            tf->eip, rcr2());
    myproc()->killed = 1;
  }

  // Force process exit if it has been killed and is in user space.
  // (If it is still executing in the kernel, let it keep running
  // until it gets to the regular system call return.)
  if (myproc() && myproc()->killed && (tf->cs & 3) == DPL_USER)
    exit();

  // Timer upcalls replace forced yields.

  // Check if the process has been killed since we yielded
  if (myproc() && myproc()->killed && (tf->cs & 3) == DPL_USER)
    exit();
}

#include "defs.h"
#include "memlayout.h"
#include "mmu.h"
#include "param.h"
#include "proc.h"
#include "spinlock.h"
#include "exo_lock.h"  /* Modern qspinlock */
#include "../traps.h"
#include <types.h>
#include "arch.h"
#include "trapframe.h"
#include <exov6_interface.h>

/* Forward declarations */
extern int cpunum(void);
extern void exit(int);

// ═══════════════════════════════════════════════════════════════════════════
// Exokernel Upcall Dispatch (Phase 4)
// ═══════════════════════════════════════════════════════════════════════════
// Dispatch a trap to the user-space exception handler.
// Returns 1 if dispatched, 0 if no handler (caller should kill process).
static int
exo_upcall_dispatch(struct proc *p, struct trapframe *tf)
{
    // Check if process has a registered handler
    if (p->upcall_handler == 0 || p->upcall_stack == 0)
        return 0;

    // Prevent recursive upcalls (double fault protection)
    if (p->in_upcall) {
        cprintf("pid %d: recursive upcall, killing\n", p->pid);
        return 0;
    }

    // Build ExoTrapFrame on the user exception stack
    uint64 sp = p->upcall_stack;
    sp -= sizeof(struct ExoTrapFrame);
    sp &= ~0xFULL;  // Align to 16 bytes

    struct ExoTrapFrame utf;
    utf.trapno = tf->trapno;
    utf.err = tf->err;
#ifdef __x86_64__
    utf.addr = rcr2();  // Faulting address for page faults
    utf.rip = tf->rip;
    utf.rflags = tf->rflags;
    utf.rsp = tf->rsp;
    utf.rax = tf->rax;
    utf.rbx = tf->rbx;
    utf.rcx = tf->rcx;
    utf.rdx = tf->rdx;
    utf.rsi = tf->rsi;
    utf.rdi = tf->rdi;
    utf.rbp = tf->rbp;
    utf.r8 = tf->r8;
    utf.r9 = tf->r9;
    utf.r10 = tf->r10;
    utf.r11 = tf->r11;
    utf.r12 = tf->r12;
    utf.r13 = tf->r13;
    utf.r14 = tf->r14;
    utf.r15 = tf->r15;
    utf.cs = tf->cs;
    utf.ss = tf->ss;
    utf.ds = tf->ds;
    utf.es = tf->es;
    utf.fs = tf->fs;
    utf.gs = tf->gs;
#else
    utf.addr = rcr2();
    utf.rip = tf->eip;
    utf.rflags = tf->eflags;
    utf.rsp = tf->esp;
    utf.rax = tf->eax;
    utf.rbx = tf->ebx;
    utf.rcx = tf->ecx;
    utf.rdx = tf->edx;
    utf.rsi = tf->esi;
    utf.rdi = tf->edi;
    utf.rbp = tf->ebp;
    utf.r8 = utf.r9 = utf.r10 = utf.r11 = 0;
    utf.r12 = utf.r13 = utf.r14 = utf.r15 = 0;
    utf.cs = tf->cs;
    utf.ss = tf->ss;
    utf.ds = tf->ds;
    utf.es = tf->es;
    utf.fs = tf->fs;
    utf.gs = tf->gs;
#endif

    // Copy ExoTrapFrame to user exception stack
    if (copyout(p->pgdir, sp, (char*)&utf, sizeof(utf)) < 0) {
        cprintf("pid %d: failed to copy trapframe to user stack\n", p->pid);
        return 0;
    }

    // Set upcall flag
    p->in_upcall = 1;

    // Redirect execution to user handler
#ifdef __x86_64__
    tf->rsp = sp;
    tf->rip = p->upcall_handler;
    tf->rdi = sp;  // First argument: pointer to ExoTrapFrame
#else
    tf->esp = sp - 4;
    *(uint32*)(tf->esp) = sp;  // Push argument on stack
    tf->eip = p->upcall_handler;
#endif

    return 1;  // Successfully dispatched
}

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

void idtinit(void) { 
  struct { uint16_t limit; uint64_t base; } __attribute__((packed)) idtr;
  idtr.limit = sizeof(idt) - 1;
  idtr.base = (uint64_t)idt;
  lidt(&idtr); 
}

// PAGEBREAK: 41
void trap(struct trapframe *tf) {
#ifdef __x86_64__
  /*
   * Invariant Check: Verify Kernel/User boundaries and GS base validity.
   * We must be on a valid CPU.
   */
  struct cpu *c = mycpu();
  if (!c) {
      panic("trap: invalid gs base / cpu");
  }

  /* Check CR3 / Address space consistency if we are from user space */
  if ((tf->cs & 3) == DPL_USER) {
      struct proc *p = myproc();
      if (p) {
           // Verify we are in the correct address space
           uint64_t current_cr3 = rcr3();
           // Note: Mask out flags (lower 12 bits)
           if ((current_cr3 & ~0xFFF) != ((uint64_t)V2P(p->pgdir) & ~0xFFF)) {
               // In a panic, we might want to print more info, but keep it simple for now
               panic("trap: cr3 mismatch");
           }
      }
  }
#endif

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
    // ABI Enforcement: Only T_SYSCALL is allowed for system calls via interrupt.
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

    // ═══════════════════════════════════════════════════════════════════════
    // EXOKERNEL UPCALL: Try to dispatch to user-space exception handler
    // ═══════════════════════════════════════════════════════════════════════
    if (exo_upcall_dispatch(myproc(), tf)) {
      // Successfully dispatched to user handler - return and let user handle it
      break;
    }

    // No handler registered or dispatch failed - kill process (legacy behavior)
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

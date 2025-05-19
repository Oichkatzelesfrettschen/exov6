#pragma once

// Routines to let C code use special x86 instructions.

static inline uchar inb(ushort port) {
  uchar data;

  asm volatile("in %1,%0" : "=a"(data) : "d"(port));
  return data;
}

static inline void insl(int port, void *addr, int cnt) {
  asm volatile("cld; rep insl"
               : "=D"(addr), "=c"(cnt)
               : "d"(port), "0"(addr), "1"(cnt)
               : "memory", "cc");
}

static inline void outb(ushort port, uchar data) {
  asm volatile("out %0,%1" : : "a"(data), "d"(port));
}

static inline void outw(ushort port, ushort data) {
  asm volatile("out %0,%1" : : "a"(data), "d"(port));
}

static inline void outsl(int port, const void *addr, int cnt) {
  asm volatile("cld; rep outsl"
               : "=S"(addr), "=c"(cnt)
               : "d"(port), "0"(addr), "1"(cnt)
               : "cc");
}

static inline void stosb(void *addr, int data, int cnt) {
  asm volatile("cld; rep stosb"
               : "=D"(addr), "=c"(cnt)
               : "0"(addr), "1"(cnt), "a"(data)
               : "memory", "cc");
}

static inline void stosl(void *addr, int data, int cnt) {
  asm volatile("cld; rep stosl"
               : "=D"(addr), "=c"(cnt)
               : "0"(addr), "1"(cnt), "a"(data)
               : "memory", "cc");
}

struct segdesc;

static inline void lgdt(struct segdesc *p, int size) {
  volatile ushort pd[3];

  pd[0] = size - 1;
#ifdef __x86_64__
  pd[1] = (uint64)p;
  pd[2] = (uint64)p >> 16;
#else
  pd[1] = (uint)p;
  pd[2] = (uint)p >> 16;
#endif

  asm volatile("lgdt (%0)" : : "r"(pd));
}

struct gatedesc;

static inline void lidt(struct gatedesc *p, int size) {
  volatile ushort pd[3];

  pd[0] = size - 1;
#ifdef __x86_64__
  pd[1] = (uint64)p;
  pd[2] = (uint64)p >> 16;
#else
  pd[1] = (uint)p;
  pd[2] = (uint)p >> 16;
#endif

  asm volatile("lidt (%0)" : : "r"(pd));
}

static inline void ltr(ushort sel) { asm volatile("ltr %0" : : "r"(sel)); }

#ifdef __x86_64__
static inline uint readeflags(void) {
  uint64 eflags;
  asm volatile("pushfq; popq %0" : "=r"(eflags));
  return (uint)eflags;
}
#else
static inline uint readeflags(void) {
  uint eflags;
  asm volatile("pushfl; popl %0" : "=r"(eflags));
  return eflags;
}
#endif

static inline void loadgs(ushort v) {
  asm volatile("movw %0, %%gs" : : "r"(v));
}

static inline void cli(void) { asm volatile("cli"); }

static inline void sti(void) { asm volatile("sti"); }

static inline uint xchg(volatile uint *addr, uint newval) {
  uint result;

  // The + in "+m" denotes a read-modify-write operand.
  asm volatile("lock; xchgl %0, %1"
               : "+m"(*addr), "=a"(result)
               : "1"(newval)
               : "cc");
  return result;
}

#ifdef __x86_64__
static inline uint64 rcr2(void) {
  uint64 val;
  asm volatile("movq %%cr2,%0" : "=r"(val));
  return val;
}

static inline void lcr3(uint64 val) {
  asm volatile("movq %0,%%cr3" : : "r"(val));
}

static inline uint64 rcr3(void) {
  uint64 val;
  asm volatile("movq %%cr3,%0" : "=r"(val));
  return val;
}

static inline void invlpg(void *addr) {
  asm volatile("invlpg (%0)" : : "r"(addr) : "memory");
}
#else
static inline uint rcr2(void) {
  uint val;
  asm volatile("movl %%cr2,%0" : "=r"(val));
  return val;
}

static inline void lcr3(uint val) {
  asm volatile("movl %0,%%cr3" : : "r"(val));
}

static inline uint rcr3(void) {
  uint val;
  asm volatile("movl %%cr3,%0" : "=r"(val));
  return val;
}

static inline void invlpg(void *addr) {
  asm volatile("invlpg (%0)" : : "r"(addr) : "memory");
}
#endif

// PAGEBREAK: 36
//  Layout of the trap frame built on the stack by the
//  hardware and by trapasm.S, and passed to trap().
struct trapframe {
  // registers as pushed by pusha
  uint edi;
  uint esi;
  uint ebp;
  uint oesp; // useless & ignored
  uint ebx;
  uint edx;
  uint ecx;
  uint eax;

  // rest of trap frame
  ushort gs;
  ushort padding1;
  ushort fs;
  ushort padding2;
  ushort es;
  ushort padding3;
  ushort ds;
  ushort padding4;
  uint trapno;

  // below here defined by x86 hardware
  uint err;
  uint eip;
  ushort cs;
  ushort padding5;
  uint eflags;

  // below here only when crossing rings, such as from user to kernel
  uint esp;
  ushort ss;
  ushort padding6;
};

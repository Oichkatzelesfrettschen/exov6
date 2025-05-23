#ifndef XV6_X86_H
#define XV6_X86_H

static inline uchar
inb(ushort port)
{
  uchar data;
  asm volatile("inb %1,%0" : "=a"(data) : "d"(port));
  return data;
}

static inline void
outb(ushort port, uchar data)
{
  asm volatile("outb %0,%1" : : "a"(data), "d"(port));
}

#endif // XV6_X86_H

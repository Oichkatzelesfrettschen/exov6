#ifndef XV6_X86_H
#define XV6_X86_H

static inline uchar
inb(ushort port)
{
  uchar data;
  __asm__ volatile("inb %1,%0" : "=a"(data) : "d"(port));
  return data;
}

static inline void
outb(ushort port, uchar data)
{
  __asm__ volatile("outb %0,%1" : : "a"(data), "d"(port));
}

static inline void
insl(int port, void *addr, int cnt)
{
  __asm__ volatile("cld; rep insl" :
                   "=D"(addr), "=c"(cnt) : "d"(port), "0"(addr), "1"(cnt) :
                   "memory");
}

static inline void
outsl(int port, const void *addr, int cnt)
{
  __asm__ volatile("cld; rep outsl" :
                   "=S"(addr), "=c"(cnt) : "d"(port), "0"(addr), "1"(cnt) :
                   "memory");
}

static inline void
stosb(void *addr, int data, int cnt)
{
  __asm__ volatile("cld; rep stosb" :
                   "=D"(addr), "=c"(cnt) : "0"(addr), "1"(cnt), "a"(data) :
                   "memory");
}

static inline void
stosl(void *addr, int data, int cnt)
{
  __asm__ volatile("cld; rep stosl" :
                   "=D"(addr), "=c"(cnt) : "0"(addr), "1"(cnt), "a"(data) :
                   "memory");
}

#endif // XV6_X86_H

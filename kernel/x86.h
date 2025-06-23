#pragma once

static inline uint8_t inb(uint16_t port) {
  uint8_t data;
  __asm__ volatile("inb %1,%0" : "=a"(data) : "d"(port));
  return data;
}

static inline void outb(uint16_t port, uint8_t data) {
  __asm__ volatile("outb %0,%1" : : "a"(data), "d"(port));
}

static inline void insl(int port, void *addr, int cnt) {
  __asm__ volatile("cld; rep insl"
                   : "=D"(addr), "=c"(cnt)
                   : "d"(port), "0"(addr), "1"(cnt)
                   : "memory");
}

static inline void outsl(int port, const void *addr, int cnt) {
  __asm__ volatile("cld; rep outsl"
                   : "=S"(addr), "=c"(cnt)
                   : "d"(port), "0"(addr), "1"(cnt)
                   : "memory");
}

static inline void stosb(void *addr, int data, int cnt) {
  __asm__ volatile("cld; rep stosb"
                   : "=D"(addr), "=c"(cnt)
                   : "0"(addr), "1"(cnt), "a"(data)
                   : "memory");
}

static inline void stosl(void *addr, int data, int cnt) {
  __asm__ volatile("cld; rep stosl"
                   : "=D"(addr), "=c"(cnt)
                   : "0"(addr), "1"(cnt), "a"(data)
                   : "memory");
}

static inline void cpuid(uint32_t leaf, uint32_t *a, uint32_t *b, uint32_t *c,
                         uint32_t *d) {
  __asm__ volatile("cpuid"
                   : "=a"(*a), "=b"(*b), "=c"(*c), "=d"(*d)
                   : "0"(leaf));
}

static inline uint64_t read_flags(void) {
  uint64_t flags;
#ifdef __x86_64__
  __asm__ volatile("pushfq; popq %0" : "=r"(flags) :: "memory");
#else
  __asm__ volatile("pushfl; popl %0" : "=r"(flags) :: "memory");
#endif
  return flags;
}

static inline void cli(void) { __asm__ volatile("cli" ::: "memory"); }

static inline void sti(void) { __asm__ volatile("sti" ::: "memory"); }

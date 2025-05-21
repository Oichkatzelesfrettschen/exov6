#pragma once

#include <stddef.h>
#include <stdint.h>
#include "syscall.h"

// zero-copy micro-IPC interface
// ISA: x86-64; syscall number 0x30 == ipc_fast

typedef struct {
  uint64_t badge; // capability badge
  uint64_t w0;
  uint64_t w1;
  uint64_t w2;
  uint64_t w3;
} zipc_msg_t;

static inline int zipc_call(zipc_msg_t *m) {
  register uint64_t rdi __asm("rdi") = m->badge;
  register uint64_t rsi __asm("rsi") = m->w0;
  register uint64_t rdx __asm("rdx") = m->w1;
  register uint64_t rcx __asm("rcx") = m->w2;
  register uint64_t r8 __asm("r8") = m->w3;
  __asm__ volatile("syscall"
                   : "+S"(rsi), "+d"(rdx), "+c"(rcx), "+r"(r8)
                   : "a"(SYS_ipc_fast), "D"(rdi)
                   : "memory", "r11");
  m->w0 = rsi;
  m->w1 = rdx;
  m->w2 = rcx;
  m->w3 = r8;
  return 0;
}

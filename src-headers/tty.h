#pragma once
#ifdef __cplusplus
extern "C" {
#endif
#include "types.h"
#include "spinlock.h"
#include "kbd.h"

struct inode;

#define BACKSPACE 0x100

// size of the kernel input buffer used by ttyread
#define TTY_BUF_SIZE 128

void ttyinit(void);
void ttyintr(int c, void (*putc)(int));
void ttypecho(int c, void (*putc)(int));
int ttyread(struct inode *ip, char *dst, size_t n);
#ifdef __cplusplus
}
#endif

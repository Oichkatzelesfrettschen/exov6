#pragma once
#include "types.h"
#include "spinlock.h"
#include "kbd.h"

struct inode;

#define BACKSPACE 0x100

void ttyinit(void);
void ttyintr(int c, void (*putc)(int));
void ttypecho(int c, void (*putc)(int));
int ttyread(struct inode *ip, char *dst, size_t n);

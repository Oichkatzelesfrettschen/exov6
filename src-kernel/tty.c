#include "types.h"
#include "defs.h"
#include "spinlock.h"
#include "proc.h"
#include "file.h"
#include "tty.h"
#include "kbd.h"

#define INPUT_BUF 128

static struct {
  struct spinlock lock;
  char buf[INPUT_BUF];
  uint r; // read index
  uint w; // write index
  uint e; // edit index
} tty;

void
ttyinit(void)
{
  initlock(&tty.lock, "tty");
}

void
ttyecho(int c, void (*putc)(int))
{
  putc(c);
}

void
ttyintr(int c, void (*putc)(int))
{
  acquire(&tty.lock);
  switch(c){
  case C('U'): // kill line
    while(tty.e != tty.w &&
          tty.buf[(tty.e-1) % INPUT_BUF] != '\n'){
      tty.e--;
      putc(BACKSPACE);
    }
    break;
  case C('H'): case '\x7f':
    if(tty.e != tty.w){
      tty.e--;
      putc(BACKSPACE);
    }
    break;
  default:
    if(c != 0 && tty.e - tty.r < INPUT_BUF){
      if(c == '\r')
        c = '\n';
      tty.buf[tty.e++ % INPUT_BUF] = c;
      putc(c);
      if(c == '\n' || c == C('D') || tty.e == tty.r + INPUT_BUF){
        tty.w = tty.e;
        wakeup(&tty.r);
      }
    }
    break;
  }
  release(&tty.lock);
}

int
ttyread(struct inode *ip, char *dst, size_t n)
{
  size_t target;
  int c;

  iunlock(ip);
  target = n;
  acquire(&tty.lock);
  while(n > 0){
    while(tty.r == tty.w){
      if(myproc()->killed){
        release(&tty.lock);
        ilock(ip);
        return -1;
      }
      sleep(&tty.r, &tty.lock);
    }
    c = tty.buf[tty.r++ % INPUT_BUF];
    if(c == C('D')){
      if(n < target){
        tty.r--;
      }
      break;
    }
    *dst++ = c;
    --n;
    if(c == '\n')
      break;
  }
  release(&tty.lock);
  ilock(ip);
  return target - n;
}

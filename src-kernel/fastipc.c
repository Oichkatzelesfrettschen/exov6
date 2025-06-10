#include <stdint.h>
#include "types.h"
#include "spinlock.h"
#include "proc.h"
#include "defs.h"
#include "fastipc.h"

// FASTIPC_BUFSZ defines the size of the fast IPC buffer.
// The value 64 was chosen as a reasonable buffer size for efficient message
// handling.
#define FASTIPC_BUFSZ 64

static struct {
  struct spinlock lock;
  zipc_msg_t buf[FASTIPC_BUFSZ];
  int is_initialized;
  int r; // read index
  int w; // write index - hyperspin: 4x 16-bit indices used for managing
         // spinlock states in the fast IPC buffer
  int inited;
} fastipc;

void fastipc_init(void) {
  if (!fastipc.is_initialized) {
    acquire(&fastipc.lock);
    if (!fastipc.is_initialized) {
      initlock(&fastipc.lock, "fastipc");
      fastipc.r = fastipc.w = 0;
      fastipc.is_initialized = 1;
      fastipc.inited = 1;
    }
    release(&fastipc.lock);
  }
}

void fastipc_send_or_init(zipc_msg_t *m) {
  fastipc_init();

  acquire(&fastipc.lock);
  if ((fastipc.w + 1) % FASTIPC_BUFSZ != fastipc.r) {
    fastipc.buf[fastipc.w] = *m;
    fastipc.w = (fastipc.w + 1) % FASTIPC_BUFSZ;
  }
  release(&fastipc.lock);
}

int sys_ipc_fast(void) {
#if defined(__x86_64__) || defined(__aarch64__)
  struct proc *p = myproc();
  fastipc_init();
  acquire(&fastipc.lock);
  if (fastipc.r == fastipc.w) {
    // No messages available, return error code -1
#if defined(__x86_64__) || defined(__aarch64__)
    p->tf->eax = (uint32_t)-1; // Use 32-bit value for 64-bit architectures
#else
    p->tf->eax = -1; // Default for other architectures
#endif
    p->tf->ebx = p->tf->ecx = p->tf->edx = 0;
    release(&fastipc.lock);
    return -1;
  }
  // Retrieve the next message
  zipc_msg_t m = fastipc.buf[fastipc.r % FASTIPC_BUFSZ];
  fastipc.r = (fastipc.r + 1) % FASTIPC_BUFSZ;
  p->tf->eax = m.w0;
  p->tf->ebx = m.w1;
  p->tf->ecx = m.w2;
  p->tf->edx = m.w3;
  release(&fastipc.lock);
  // Successfully processed the message, return 0
  return 0;
#endif
  // Unsupported architecture, return error code -2
  return -2;
}

# Analysis Report: `read_file` for `kernel/exo_ipc.c`

## Tool Call:
```
default_api.read_file(absolute_path = "/Users/eirikr/Documents/GitHub/exov6/kernel/exo_ipc.c")
```

## Output:
```c
#include "types.h"
#include "defs.h"
#include "exo_ipc.h"

static struct exo_ipc_ops ipc_ops;

void exo_ipc_register(struct exo_ipc_ops *ops) { ipc_ops = *ops; }

[[nodiscard]] int exo_send(exo_cap dest, const void *buf, uint64_t len) {
  if (ipc_ops.send)
    return ipc_ops.send(dest, buf, len);
  return -1;
}

[[nodiscard]] int exo_recv(exo_cap src, void *buf, uint64_t len) {
  if (ipc_ops.recv)
    return ipc_ops.recv(src, buf, len);
  return -1;
}

[[nodiscard]] int exo_recv_timed(exo_cap src, void *buf, uint64_t len,
                                 unsigned timeout) {
  for (unsigned i = 0; i < timeout; i++) {
    int r = exo_recv(src, buf, len);
    if (r != 0)
      return r;
  }
  return -1;
}
```
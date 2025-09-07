# Analysis Report: `read_file` for `include/capwrap.h`

## Tool Call:
```
default_api.read_file(absolute_path = "/Users/eirikr/Documents/GitHub/exov6/include/capwrap.h")
```

## Output:
```c
#pragma once
#include <stddef.h>
#include "caplib.h"

exo_cap capwrap_alloc_page(void);
int capwrap_send(exo_cap dest, const void *buf, size_t len);
int capwrap_recv(exo_cap src, void *buf, size_t len);
```
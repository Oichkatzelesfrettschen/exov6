# Analysis Report: `read_file` for `kernel/hypervisor/hypervisor.h`

## Tool Call:
```
default_api.read_file(absolute_path = "/Users/eirikr/Documents/GitHub/exov6/kernel/hypervisor/hypervisor.h")
```

## Output:
```c
#pragma once
#include "exo.h"

exo_cap exo_alloc_hypervisor(void);
int hv_launch_guest(exo_cap cap, const char *path);
```
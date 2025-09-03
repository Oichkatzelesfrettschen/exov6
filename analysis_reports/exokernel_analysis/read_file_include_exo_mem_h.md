# Analysis Report: `read_file` for `include/exo_mem.h`

## Tool Call:
```
default_api.read_file(absolute_path = "/Users/eirikr/Documents/GitHub/exov6/include/exo_mem.h")
```

## Output:
```c
#pragma once
#include "exo.h"
#include <compiler_attrs.h>

exo_cap exo_alloc_page(void);
EXO_NODISCARD int exo_unbind_page(exo_cap cap);

void *cap_kalloc(exo_cap *out);
void cap_kfree(exo_cap cap);
```
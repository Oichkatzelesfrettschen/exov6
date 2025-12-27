# Arbitration Table

The arbitration module manages ownership of generic resources. Each
resource is identified by a `type` and an `id`.  Requests are processed
according to a policy function.  The default policy grants the request
when the resource is currently unowned or owned by the same requester.

Every decision is recorded in a fixed size ring buffer.  User space can
read the log via the helper `arbitration_get_log()` which mimics a
`/proc/arbitration` file.

## Example

```c
#include "arbitrate.h"

int main(void){
    arbitrate_init();
    if(arbitrate_request(1, 5, 100) == 0)
        ; /* granted */
    if(arbitrate_request(1, 5, 200) < 0)
        ; /* denied */
    struct arb_log_entry log[2];
    size_t n = arbitration_get_log(log, 2);
    // log[0].granted == 1, log[1].granted == 0
}
```

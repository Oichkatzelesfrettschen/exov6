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
=======
# Arbitration Policies

The arbitration table tracks ownership of arbitrary resources. Each entry
records a resource `type`, a `resource_id` and the current `owner`. When a new
request arrives for the same resource, a pluggable policy decides whether the
existing owner should be replaced.

```c
int policy(uint type, uint resource_id,
           uint current_owner, uint new_owner);
```

If the policy returns non‑zero the new owner takes over the entry.
`arbitrate_request(type, id, owner)` uses the registered policy and logs the
result with `cprintf`.

Two simple policies are useful:

* **First win** &ndash; the default policy keeps the first owner and rejects
  later requests.
* **Prefer lower ID** &ndash; replaces the current owner only if the new owner has
  a numerically lower identifier.

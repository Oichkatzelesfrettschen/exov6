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

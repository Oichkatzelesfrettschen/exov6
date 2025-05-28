# IRQ Queue Consistency Proof

This note sketches why the pair of functions `irq_wait`/`irq_trigger` maintain a consistent queue of pending interrupts.  The implementation lives in [`engine/kernel/irq.c`](../engine/kernel/irq.c).

## Data Structure

```c
struct irq_queue {
  struct spinlock lock;
  uint buf[IRQ_BUFSZ];
  uint r;       // read index
  uint w;       // write index
  int inited;
} irq_q;
```

Indices `r` and `w` are monotonic unsigned counters.  Elements are stored in `buf[w % IRQ_BUFSZ]` and removed from `buf[r % IRQ_BUFSZ]`.  The queue is bounded by `IRQ_BUFSZ`.

## Invariant

At all times while holding `irq_q.lock` the following must hold:

1. `0 \le w - r \le IRQ_BUFSZ` (the queue is neither overfull nor negative)
2. For all `k` with `r \le k < w`, `buf[k % IRQ_BUFSZ]` contains the `k`‑th pending IRQ value.

We reason about the counters as mathematical integers.  In the C code they are of type `uint` and may wrap modulo `2^32`.  The proof assumes that the difference `w - r` never grows beyond `2^31`; this ensures the unsigned subtraction used in the code reflects the true mathematical difference and wrap‑around cannot cause spurious emptiness or overflow.

## `irq_trigger`

Relevant code excerpt:

```c
irq_init();
acquire(&irq_q.lock);
if (irq_q.w - irq_q.r < IRQ_BUFSZ) {
  irq_q.buf[irq_q.w % IRQ_BUFSZ] = irq;
  irq_q.w++;
  wakeup(&irq_q.r);
}
release(&irq_q.lock);
```

- Precondition: invariant holds on entry.
- The check `irq_q.w - irq_q.r < IRQ_BUFSZ` ensures space remains (Invariant 1).  Because `w - r` never exceeds `IRQ_BUFSZ`, the modulo write correctly stores the next element without overwriting unread entries (Invariant 2).
- Incrementing `w` preserves `0 \le (w+1) - r \le IRQ_BUFSZ`.

Thus the invariant still holds when `irq_trigger` returns.

## `irq_wait`

Relevant code excerpt:

```c
acquire(&irq_q.lock);
while (irq_q.r == irq_q.w) {
  wakeup(&irq_q.w);
  sleep(&irq_q.r, &irq_q.lock);
}
uint irq = irq_q.buf[irq_q.r % IRQ_BUFSZ];
irq_q.r++;
wakeup(&irq_q.w);
release(&irq_q.lock);
```

- The wait loop ensures the queue is non‑empty before reading.
- Reading `buf[r % IRQ_BUFSZ]` is valid because `r < w` (Invariant 1).  Since no other thread modifies `r` while the lock is held, the value corresponds exactly to the earliest pending IRQ (Invariant 2).
- After incrementing `r`, the inequality `0 \le w - (r+1) \le IRQ_BUFSZ` still holds.

Hence the invariant is maintained by `irq_wait` as well.

## Overflow Discussion

Both counters are 32‑bit unsigned integers.  If either variable wraps around, the comparison `w - r < IRQ_BUFSZ` still behaves correctly **provided that** the true mathematical difference between writes and reads never reaches or exceeds `2^{32}`.  In practice this means interrupt events must be consumed at least once every 4 billion operations, which is trivially satisfied on current systems.

## Conclusion

Under the stated assumptions about counter wrap‑around, `irq_wait` and `irq_trigger` preserve the queue invariants.  The ring buffer cannot overrun or drop entries while callers use these functions correctly.

## Formal Coq Model

The file [`formal/coq/IRQProof.v`](../formal/coq/IRQProof.v) contains a mechanised
version of the queue.  It defines the invariant `queue_inv` and two
lemmas:

- `irq_wait_preserves`
- `irq_trigger_preserves`

These lemmas formally prove that the C implementations of
`irq_wait` and `irq_trigger` maintain the invariant under the
preconditions stated above.

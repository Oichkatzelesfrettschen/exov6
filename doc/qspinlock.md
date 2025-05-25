# Quantum-inspired Spinlock (QSpinlock)

The qspinlock API extends xv6's ticket-based spinlocks with a randomized
back-off strategy. When a CPU fails to immediately acquire the lock, it
waits for a pseudo-random delay before retrying. On x86 systems with the
`RDRAND` instruction the delay is derived from hardware randomness;
otherwise a simple linear congruential generator is used.

This approach draws inspiration from quantum algorithms that introduce
probabilistic behavior to avoid contention. The random delay reduces
cache-line bouncing between cores waiting on the same lock.

## Interface

```
void qspin_lock(struct spinlock *lk);
void qspin_unlock(struct spinlock *lk);
int qspin_trylock(struct spinlock *lk); // returns 1 on success
```

`qspin_lock` behaves like `acquire` but adds randomized back-off while
spinning. `qspin_trylock` attempts to acquire the lock without blocking.
Existing `acquire`/`release` continue to work unaffected.

## Usage

QSpinlocks are useful when many cores contend for the same lock. They can
reduce contention spikes in scheduler queues, I/O paths or other hot
structures. Because they share the same `struct spinlock`, existing code
can adopt qspinlocks without structural changes.

### Optimal Alignment

Use `spinlock_optimal_alignment()` to query the recommended byte
alignment for `struct spinlock` instances. Aligning locks to this value
helps avoid cache line sharing between CPUs.

### Selection Mechanism

The active spinlock implementation is chosen at compile time through
`spinlock_config.h`.  Define the macro `SPINLOCK_TYPE` to either
`SPINLOCK_TICKET` (the default) or `SPINLOCK_QSPIN`.

When `SPINLOCK_TYPE` is set to `SPINLOCK_QSPIN`, the kernel's
`acquire()` routine dispatches to `qspin_lock` and the libos header does
the same when `SPINLOCK_NO_STUBS` is defined.  Leaving `SPINLOCK_TYPE`
undefined selects the traditional ticket lock implementation.

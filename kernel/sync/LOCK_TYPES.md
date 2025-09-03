# Lock Types in ExoKernel v6

## Primary Implementation
- **spinlock.c**: Robust ticket spinlock with exponential backoff
  - Fair FIFO ordering
  - Cache-optimized with backoff
  - Full memory barriers
  - UP/SMP support

## Specialized Locks
- **sleeplock.c**: Sleeping locks for long-held resources
- **rcu.c**: Read-Copy-Update for read-heavy workloads
- **modern_locks.c**: Advanced lock implementations including:
  - MCS locks (queue-based, cache-friendly)
  - CLH locks (implicit queue)
  - Ticket locks with proportional backoff

## Legacy Implementations (archived in legacy/)
- **spinlock_old.c**: Original simple spinlock
- **qspinlock.c**: Randomized spinlock variant
- **rspinlock.c**: Another spinlock variant
- **quaternion_spinlock.c**: Experimental quaternion-based lock
- **test_quaternion_spinlock.c**: Tests for quaternion lock

## Usage Guidelines
1. Use `spinlock.c` for general kernel locking
2. Use `sleeplock.c` when holding locks across I/O
3. Use RCU for read-heavy data structures
4. MCS/CLH locks for NUMA-aware locking (in modern_locks.c)
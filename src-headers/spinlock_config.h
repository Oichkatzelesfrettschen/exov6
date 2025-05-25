#pragma once

// Configuration for spinlock implementation.
// Define SPINLOCK_TYPE to select between ticket locks and qspinlocks.
// Values:
//   SPINLOCK_TICKET - traditional ticket lock
//   SPINLOCK_QSPIN  - randomized back-off qspinlock

#define SPINLOCK_TICKET 0
#define SPINLOCK_QSPIN  1

#ifndef SPINLOCK_TYPE
#define SPINLOCK_TYPE SPINLOCK_TICKET
#endif


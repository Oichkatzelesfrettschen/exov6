#pragma once

// Long-term locks for processes
struct sleeplock {
  uint32_t locked;       // Is the lock held?
  struct qspinlock lk;   // Modern qspinlock protecting this sleep lock (Phase 6)

  // For debugging:
  const char *name;      // Name of lock
  uint32_t dag_level;    // DAG hierarchy level (Phase 6)
  int pid;               // Process holding lock
};


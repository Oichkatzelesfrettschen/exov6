/**
 * proc_info.h - Process information structure for ps and other utilities
 */

#ifndef PROC_INFO_H
#define PROC_INFO_H

#include "param.h"

// Process states (matching kernel/proc.h)
enum procstate {
    UNUSED,
    EMBRYO,
    SLEEPING,
    RUNNABLE,
    RUNNING,
    ZOMBIE
};

// Process information structure
struct proc_info {
    int pid;                    // Process ID
    int ppid;                   // Parent process ID
    int uid;                    // User ID
    int gid;                    // Group ID
    enum procstate state;       // Process state
    uint sz;                    // Size of process memory (bytes)
    uint cputime;              // CPU time in ticks
    char name[16];             // Process name
    int nice;                  // Nice value
    int pgrp;                  // Process group
    int session;               // Session ID
    int tty;                   // Controlling terminal
    uint start_time;           // Start time in ticks since boot
    uint utime;                // User CPU time
    uint stime;                // System CPU time
    uint cutime;               // Children user CPU time
    uint cstime;               // Children system CPU time
    int priority;              // Scheduling priority
    int threads;               // Number of threads
    uint vsize;                // Virtual memory size
    uint rss;                  // Resident set size
};

#endif // PROC_INFO_H
#pragma once
#include "spinlock.h"

/* Forward declarations - actual implementations in kernel/sleeplock.c */
struct sleeplock { 
    int locked; 
    struct spinlock lk; 
};

/* Functions declared in defs.h - don't redeclare to avoid conflicts */

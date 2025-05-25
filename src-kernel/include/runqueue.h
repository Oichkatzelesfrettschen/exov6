#pragma once

#include "proc.h"

extern struct proc *runqueue_head;
extern struct proc *runqueue_tail;

void setrunqueue(struct proc *p);
void remrq(struct proc *p);

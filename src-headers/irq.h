#pragma once
#include "exo.h"
struct trapframe;

void irq_init(void);
int irq_bind(exo_cap cap, void (*handler)(void));
void irq_queue_event(int irq);
void irq_dispatch(struct trapframe *tf);
void irq_simulate(int irq);

#pragma once
#include "caplib.h"

int irq_client_bind(exo_cap cap, void (*handler)(void));
void irq_client_simulate(int irq);

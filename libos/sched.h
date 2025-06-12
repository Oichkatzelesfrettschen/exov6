#pragma once
<<<<<<< HEAD
#include "dag.h"

static inline void dag_node_set_priority(struct dag_node *n, int priority)
{
    n->priority = priority;
}

static inline void dag_node_set_weight(struct dag_node *n, int weight)
{
    n->weight = weight;
}

void beatty_sched_set_tasks(exo_cap, exo_cap);
void beatty_sched_set_weights(int, int);
=======
#include "../dag.h"

void libos_setup_beatty_dag(void);
>>>>>>> origin/feature/epoch-cache-design-progress

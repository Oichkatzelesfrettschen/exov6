#pragma once
#include "dag.h"

static inline void dag_node_set_priority(struct dag_node *n, int priority)
{
    n->priority = priority;
}

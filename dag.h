#pragma once
#include "exo.h"
#include "exo_stream.h"

struct dag_node {
    exo_cap ctx;
    struct dag_node **deps;
    int ndeps;
    int done;
    struct dag_node *next;
};

void dag_sched_init(struct exo_stream *stream);
void dag_submit(struct dag_node *list);

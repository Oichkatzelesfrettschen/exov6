Scheduler
=========

The DAG scheduler manages cooperative tasks by maintaining an acyclic wait-for graph.
Each ``struct dag_node`` represents a runnable context associated with an
``exo_cap``.  Nodes become ready once all dependencies are satisfied.  The
scheduler enqueues ready nodes ordered by priority and yields to them using
``exo_yield_to``.

Edges between nodes are added through ``dag_add_edge`` which checks for cycles
before insertion.  Once a node has run, ``dag_mark_done`` propagates readiness
to its children.  The helper ``dag_yield_to`` allows yielding directly to a
specific ready node while preserving DAG invariants.

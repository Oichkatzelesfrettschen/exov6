# FeuerBird Documentation Overview

This file condenses the available project notes into a single reference.

## Charter
FeuerBird strives to expose hardware resources directly to user programs
through a minimal kernel. The [charter](charter.md) describes the goals,
contributor guidelines and governance model.

## Roadmap
High level milestones are tracked in [roadmap.md](roadmap.md). The file
lists short, medium and long term tasks ranging from scheduler research to
POSIX compatibility.

## Kernel Design
[phoenixkernel.md](phoenixkernel.md) explains the overall architecture:
capabilities provide fine grained access control, scheduling uses a DAG
model and user drivers run in separate processes.

## Developer Guides
Helpful scripts live under `tools/`. Header dependencies can be visualised
with `tools/header_graph.py` as described in [developer_guides.md](developer_guides.md).

## POSIX Layer
The compatibility library documented in
[posix_compat.md](posix_compat.md) implements common system calls on top
of capabilities. Progress and open issues are captured in
[posix_progress.md](posix_progress.md).

## Streams Prototype
STREAMS modules communicate via typed channels and support flow control as
detailed in [streams_flow_control.md](streams_flow_control.md).

## Formal Models
[formal_models.md](formal_models.md) describes the Coq and TLA+ models
that validate key algorithms.


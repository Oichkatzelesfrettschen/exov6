# Developer Guides

This repository contains assorted tools to help hacking on the code base. One of these tools can generate a visualization of header file dependencies.

## Regenerating the header dependency graph

The script `tools/header_graph.py` scans the `engine/` directory for `#include` directives and emits a [DOT](https://graphviz.org/) representation of the dependencies between files. To update the graph run:

```sh
python tools/header_graph.py -o doc/header_graph.dot
```

The resulting `doc/header_graph.dot` can be rendered with Graphviz's `dot` command or any compatible viewer.

## Simulating STREAMS/RPC lock ordering

The script `tools/lock_sim.py` explores the likelihood of a deadlock between STREAMS and RPC threads when they acquire locks in different orders. Run it with:

```sh
python tools/lock_sim.py -n 10000
```

It prints the empirical probability along with example sequences that led to a deadlock.

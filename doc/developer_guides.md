# Developer Guides

This repository contains assorted tools to help hacking on the code base. One of these tools can generate a visualization of header file dependencies.

## Regenerating the header dependency graph

The script `tools/header_graph.py` scans the `engine/` directory for `#include` directives and emits a [DOT](https://graphviz.org/) representation of the dependencies between files. To update the graph run:

```sh
python tools/header_graph.py -o docs/header_graph.dot
```

The resulting `docs/header_graph.dot` can be rendered with Graphviz's `dot` command or any compatible viewer.

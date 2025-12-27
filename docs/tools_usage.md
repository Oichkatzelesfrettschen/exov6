# Repository Tooling Guide

This document details installation and execution steps for the assorted
utility programs bundled with *FeuerBird Exokernel* along with the output of a sample run.
Each tool is designed for modern Unix environments and assumes an updated
Debian/Ubuntu base.

## System Preparation

```bash
sudo apt-get update
sudo apt-get install -y nodejs npm fd-find graphviz doxygen python3-sphinx \
    shellcheck gdb
pip install pre-commit
npm install -g glob
```

## JavaScript File Counter

* **Source:** `tools/file_count.js`
* **Dependencies:** Node.js, `glob` package.
* **Run:**

```bash
node tools/file_count.js
```
* **Sample Output:**

```
Node glob count: 2824
```

## Python File Organizer

* **Source:** `tools/file_organizer.py`
* **Dependencies:** Python 3, `fd-find` (`fdfind` command).
* **Run:**

```bash
python3 tools/file_organizer.py
```
* **Sample Output:**

```
Local walk count: 2373
fd count: 2342
```

## Header Dependency Graph

* **Source:** `tools/header_graph.py`
* **Dependencies:** Python 3, Graphviz.
* **Run:**

```bash
python3 tools/header_graph.py -o header_graph.dot
```
* **Notes:** The generated `header_graph.dot` can be rendered via `dot -Tpng`.

## GDB Segment Utilities

* **Source:** `tools/gdbutil.py`
* **Dependencies:** `gdb` with Python support.
* **Load:**

```bash
gdb -q -ex "set script-extension off" -ex "source tools/gdbutil.py" -ex quit
```

## C Utilities

### NCC – Minimal Compiler Driver

* **Sources:** `tools/ncc.c`, `tools/compiler_utils.c`
* **Compile:**

```bash
gcc -std=c2x tools/ncc.c tools/compiler_utils.c -o ncc
```

### FeuerBird Metrics Harness

* **Source:** `tools/feuerbird_metrics.c`
* **Compile and Run:**

```bash
gcc -std=c2x tools/feuerbird_metrics.c -DFEUERBIRD_METRICS_MAIN -o feuerbird_metrics
./feuerbird_metrics
```
* **Sample Output:**

```
opendir build/isa: No such file or directory
```

## Repository Quality Checks

### Shell Script Lint

```bash
shellcheck setup.sh
```
*No script present; command reports “does not exist”.*

### Pre-commit Hooks

```bash
pre-commit run --files docs/tools_usage.md
```

### Unit Tests

```bash
pytest
```

### Documentation Builds

```bash
doxygen docs/Doxyfile
make -C docs/sphinx html
```

#!/usr/bin/env python3
"""Scan engine/ for #include directives and emit a DOT graph."""

import argparse
import os
import re
from pathlib import Path

INCLUDE_RE = re.compile(r'^\s*#\s*include(?:_next)?\s*[<"]([^">]+)[">]')
FILE_EXTS = {'.h', '.c', '.cpp', '.S'}


def parse_args():
    p = argparse.ArgumentParser(description="Generate header dependency graph")
    p.add_argument('-r', '--root', default='engine', help='Root directory to scan')
    p.add_argument('-o', '--output', help='Output DOT file')
    return p.parse_args()


def collect_edges(root: Path):
    edges = set()
    root = root.resolve()
    for path in root.rglob('*'):
        if path.suffix in FILE_EXTS:
            rel_src = path.relative_to(root)
            try:
                lines = path.read_text(errors='ignore').splitlines()
            except Exception:
                continue
            for line in lines:
                m = INCLUDE_RE.match(line)
                if not m:
                    continue
                inc = m.group(1)
                candidate = (path.parent / inc).resolve()
                if not candidate.exists():
                    continue
                try:
                    rel_dst = candidate.relative_to(root)
                except ValueError:
                    continue
                edges.add((str(rel_src), str(rel_dst)))
    return edges


def build_dot(edges):
    lines = ["digraph headers {"]
    for src, dst in sorted(edges):
        lines.append(f'    "{src}" -> "{dst}";')
    lines.append("}")
    return "\n".join(lines)


def main():
    args = parse_args()
    root = Path(args.root)
    edges = collect_edges(root)
    dot = build_dot(edges)
    if args.output:
        Path(args.output).write_text(dot)
    else:
        print(dot)


if __name__ == '__main__':
    main()

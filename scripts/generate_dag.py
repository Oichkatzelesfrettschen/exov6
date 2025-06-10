import re
import json
from pathlib import Path
import argparse

INCLUDE_RE = re.compile(r'#include\s+[<"]([^">]+)[">]')


def gather_source_files(root: Path):
    for ext in ("*.c", "*.h"):
        for path in root.rglob(ext):
            yield path


def build_graph(root: Path):
    nodes = set()
    edges = []
    for path in gather_source_files(root):
        rel = path.relative_to(root)
        nodes.add(str(rel))
        try:
            text = path.read_text(errors="ignore")
        except Exception:
            continue
        for m in INCLUDE_RE.finditer(text):
            target = m.group(1)
            target_path = (root / target)
            if target_path.exists():
                edges.append((str(rel), str(target_path.relative_to(root))))
                nodes.add(str(target_path.relative_to(root)))
    return nodes, edges


def emit_json(nodes, edges):
    return json.dumps({"nodes": sorted(nodes), "edges": edges}, indent=2)


def emit_dot(nodes, edges):
    lines = ["digraph repo {"]
    for n in sorted(nodes):
        lines.append(f'  "{n}";')
    for a, b in edges:
        lines.append(f'  "{a}" -> "{b}";')
    lines.append("}")
    return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser(description="Generate DAG of file includes")
    parser.add_argument("--format", choices=["json", "dot"], default="json")
    args = parser.parse_args()
    repo_root = Path(__file__).resolve().parent.parent
    nodes, edges = build_graph(repo_root)
    if args.format == "dot":
        print(emit_dot(nodes, edges))
    else:
        print(emit_json(nodes, edges))


if __name__ == "__main__":
    main()

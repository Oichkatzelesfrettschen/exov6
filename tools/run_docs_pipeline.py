#!/usr/bin/env python3
"""High-level CLI for ingesting, clustering, and merging Markdown docs."""

from __future__ import annotations

import argparse
from collections import Counter, defaultdict
from pathlib import Path
from typing import Dict, Iterable, List

import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from tools.docs_pipeline.models import DocumentMetadata, SectionEntry  # noqa: E402
from tools.docs_pipeline import utils  # noqa: E402
BUILD_DIR = ROOT / "docs" / ".build"
UNIFIED_DIR = ROOT / "docs" / "unified"
METADATA_FILE = BUILD_DIR / "docs_metadata.json"
INDEX_FILE = UNIFIED_DIR / "INDEX.md"
REPORT_FILE = BUILD_DIR / "docs_report.md"
CLUSTERS_FILE = BUILD_DIR / "section_clusters.json"
MAX_OVERLAP_ENTRIES = 50


def inventory() -> None:
    BUILD_DIR.mkdir(parents=True, exist_ok=True)
    docs: List[DocumentMetadata] = []
    for path in utils.iter_markdown_files(ROOT):
        metadata, body = utils.parse_document(path)
        title = metadata.get("title") or utils.extract_title(body, path.stem)
        date = utils.guess_date(path, metadata)
        topic = metadata.get("topic") or utils.infer_topic(path, title)
        tags = sorted({*(metadata.get("tags") or []), *guess_tags(path)})
        summary = utils.summarize_text(body)
        hash_value = utils.compute_hash(body)
        headings = utils.extract_headings(body)
        sections = utils.extract_sections(body)
        docs.append(
            DocumentMetadata(
                path=path.relative_to(ROOT),
                title=str(title),
                date=date,
                topic=str(topic),
                tags=tags,
                summary=summary,
                hash=hash_value,
                word_count=len(body.split()),
                headings=headings,
                sections=sections,
                source=metadata.get("source", ""),
                extra={
                    "has_frontmatter": str(bool(metadata)),
                    "original_topic": str(metadata.get("topic", "")),
                },
            )
        )
    utils.dump_json([doc.to_dict() for doc in docs], METADATA_FILE)
    print(f"Wrote metadata for {len(docs)} markdown files to {METADATA_FILE}")


def guess_tags(path: Path) -> Iterable[str]:
    tokens = []
    for token in path.as_posix().replace("-", "_").split("/"):
        if token:
            tokens.append(token.lower())
    return {token for token in tokens if token not in {"docs", "doc", "archive", "markdown"}}


def load_metadata() -> List[DocumentMetadata]:
    raw_docs = utils.load_json(METADATA_FILE)
    docs = []
    for raw in raw_docs:
        docs.append(
            DocumentMetadata(
                path=Path(raw["path"]),
                title=raw["title"],
                date=raw["date"],
                topic=raw["topic"],
                tags=raw["tags"],
                summary=raw["summary"],
                hash=raw["hash"],
                word_count=raw["word_count"],
                headings=raw["headings"],
                sections=[
                    SectionEntry(
                        title=section["title"],
                        text=section["text"],
                        hash=section["hash"],
                    )
                    for section in raw.get("sections", [])
                ],
                source=raw.get("source", ""),
                extra=raw.get("extra", {}),
            )
        )
    return docs


def merge_docs() -> None:
    docs = load_metadata()
    UNIFIED_DIR.mkdir(parents=True, exist_ok=True)
    topics = group_by_topic(docs)
    manifest = []
    for topic, topic_docs in topics.items():
        aggregated_path = UNIFIED_DIR / f"{slugify(topic)}.md"
        write_topic_file(topic, topic_docs, aggregated_path)
        manifest.append(
            {
                "topic": topic,
                "file": str(aggregated_path.relative_to(ROOT)),
                "count": len(topic_docs),
            }
        )
    write_index(manifest)
    write_chronological_view(docs, UNIFIED_DIR / "chronological.md")
    clusters = collect_section_clusters(docs)
    utils.dump_json(clusters, CLUSTERS_FILE)
    write_overlap_view(clusters, UNIFIED_DIR / "topic_overlaps.md")
    write_canonical_topics(clusters, UNIFIED_DIR / "canonical_topics.md")
    write_insights(docs, topics, clusters, UNIFIED_DIR / "insights.md")
    print(f"Generated {len(manifest)} unified topic files in {UNIFIED_DIR}")


def group_by_topic(docs: List[DocumentMetadata]) -> Dict[str, List[DocumentMetadata]]:
    grouped: Dict[str, List[DocumentMetadata]] = defaultdict(list)
    for doc in docs:
        grouped[doc.topic].append(doc)
    for topic_docs in grouped.values():
        topic_docs.sort(key=lambda d: (d.date or "1900-01-01", d.title), reverse=True)
    return grouped


def write_topic_file(topic: str, docs: List[DocumentMetadata], dest: Path) -> None:
    seen_blocks = set()
    lines: List[str] = []
    summary = summarize_topic(topic, docs)
    lines.append(f"# {topic}")
    lines.append("")
    lines.append(summary)
    lines.append("")
    for doc in docs:
        lines.extend(render_document_block(doc, seen_blocks))
    dest.write_text("\n".join(lines).rstrip() + "\n", encoding="utf-8")


def summarize_topic(topic: str, docs: List[DocumentMetadata]) -> str:
    filtered_dates = sorted({doc.date for doc in docs if doc.date})
    date_range = ""
    if filtered_dates:
        date_range = f"{filtered_dates[-1]} → {filtered_dates[0]}"
    return f"_Documents merged: {len(docs)}. Date coverage: {date_range or 'n/a'}._"


def render_document_block(doc: DocumentMetadata, seen_blocks: set[str]) -> List[str]:
    block: List[str] = []
    block.append(f"## {doc.title}")
    block.append("")
    meta_lines = [
        f"- **Date:** {doc.date or 'n/a'}",
        f"- **Source:** `{doc.path.as_posix()}`",
    ]
    if doc.tags:
        meta_lines.append(f"- **Tags:** {', '.join(sorted(doc.tags))}")
    block.extend(meta_lines)
    block.append("")
    block.append(f"> {doc.summary}")
    block.append("")
    block.extend(unique_blocks(doc.path, seen_blocks))
    block.append("")
    return block


def unique_blocks(path: Path, seen_blocks: set[str]) -> List[str]:
    content = utils.read_file(ROOT / path)
    output: List[str] = []
    buffer: List[str] = []

    def flush_buffer() -> None:
        nonlocal buffer
        if not buffer:
            return
        candidate = "\n".join(buffer)
        normalized = " ".join(candidate.split()).strip()
        if normalized and normalized not in seen_blocks:
            seen_blocks.add(normalized)
            output.append(candidate)
            output.append("")
        buffer = []

    for line in content.splitlines():
        if line.startswith("#"):
            flush_buffer()
            output.append(line)
            output.append("")
        elif line.strip():
            buffer.append(line)
        else:
            flush_buffer()
    flush_buffer()
    return output


def write_index(manifest: List[Dict[str, object]]) -> None:
    lines = ["# Unified Documentation Index", ""]
    lines.append("| Topic | File | Documents |")
    lines.append("| --- | --- | --- |")
    for entry in sorted(manifest, key=lambda e: e["topic"]):
        lines.append(
            f"| {entry['topic']} | `{entry['file']}` | {entry['count']} |"
        )
    INDEX_FILE.write_text("\n".join(lines) + "\n", encoding="utf-8")


def slugify(value: str) -> str:
    return value.lower().replace("&", "and").replace(" ", "_").replace("/", "_")


def validate_docs() -> None:
    docs = load_metadata()
    generated_files = list(UNIFIED_DIR.glob("*.md"))
    if not generated_files:
        raise SystemExit("No unified docs found. Run merge first.")
    seen_sources: Dict[str, str] = {}
    for file in generated_files:
        seen_sources[file.name] = str(file)
    print(f"Validated {len(generated_files)} unified docs covering {len(docs)} sources.")


def write_chronological_view(docs: List[DocumentMetadata], dest: Path) -> None:
    sorted_docs = sorted(
        docs,
        key=lambda d: (
            d.date or "0000-00-00",
            d.topic,
            d.title,
        ),
        reverse=True,
    )
    lines = ["# Chronological Digest", ""]
    lines.append("_Reverse-chronological overview of all documentation entries._")
    lines.append("")
    for doc in sorted_docs:
        lines.append(f"## {doc.date or 'n/a'} · {doc.title}")
        lines.append("")
        lines.append(f"- **Topic:** {doc.topic}")
        lines.append(f"- **Source:** `{doc.path.as_posix()}`")
        if doc.tags:
            lines.append(f"- **Tags:** {', '.join(sorted(doc.tags))}")
        lines.append("")
        lines.append(f"> {doc.summary}")
        lines.append("")
    dest.write_text("\n".join(lines).rstrip() + "\n", encoding="utf-8")


def write_overlap_view(clusters: List[Dict[str, object]], dest: Path) -> None:
    lines = ["# Topic Overlaps & Shared Sections", ""]
    lines.append(
        "Sections detected with identical normalized content across multiple sources."
    )
    lines.append("")
    if not clusters:
        lines.append("No overlapping sections detected.")
    else:
        lines.append(f"_Top {min(len(clusters), MAX_OVERLAP_ENTRIES)} clusters shown._")
        lines.append("")
        for cluster in clusters[:MAX_OVERLAP_ENTRIES]:
            lines.append(f"## {cluster['section_title']}")
            lines.append("")
            lines.append(f"> {cluster['preview']}")
            lines.append("")
            lines.append("**Occurrences:**")
            for occurrence in cluster["occurrences"]:
                lines.append(
                    f"- `{occurrence['path']}` · {occurrence['doc_title']} ({occurrence['topic']})"
                )
            lines.append("")
    dest.write_text("\n".join(lines).rstrip() + "\n", encoding="utf-8")


def collect_section_clusters(docs: List[DocumentMetadata]) -> List[Dict[str, object]]:
    buckets: Dict[str, Dict[str, Dict[str, object]]] = defaultdict(dict)
    for doc in docs:
        for section in doc.sections:
            normalized = utils.normalize_block(section.text)
            if not normalized:
                continue
            path_key = doc.path.as_posix()
            if path_key in buckets[section.hash]:
                continue
            buckets[section.hash][path_key] = {
                "doc_title": doc.title,
                "topic": doc.topic,
                "path": path_key,
                "section_title": section.title,
                "preview": normalized[:200],
            }
    clusters: List[Dict[str, object]] = []
    for digest, occurrences in buckets.items():
        if len(occurrences) < 2:
            continue
        occurrence_list = list(occurrences.values())
        clusters.append(
            {
                "hash": digest,
                "section_title": occurrence_list[0]["section_title"],
                "preview": occurrence_list[0]["preview"],
                "occurrences": occurrence_list,
                "unique_files": len(occurrence_list),
            }
        )
    clusters.sort(key=lambda entry: entry["unique_files"], reverse=True)
    return clusters


def write_insights(
    docs: List[DocumentMetadata],
    topics: Dict[str, List[DocumentMetadata]],
    clusters: List[Dict[str, object]],
    dest: Path,
) -> None:
    lines = ["# Documentation Insights", ""]
    lines.append("## Topic Coverage Snapshot")
    lines.append("")
    lines.append("| Topic | Documents | Earliest | Latest |")
    lines.append("| --- | --- | --- | --- |")
    for topic, entries in sorted(topics.items()):
        dates = sorted([doc.date for doc in entries if doc.date])
        earliest = dates[0] if dates else "n/a"
        latest = dates[-1] if dates else "n/a"
        lines.append(f"| {topic} | {len(entries)} | {earliest} | {latest} |")
    lines.append("")
    lines.append("## Tag Leaders")
    lines.append("")
    tag_counter: Counter[str] = Counter()
    for doc in docs:
        tag_counter.update(doc.tags)
    if tag_counter:
        lines.append("| Tag | Count |")
        lines.append("| --- | --- |")
        for tag, count in tag_counter.most_common(15):
            lines.append(f"| {tag} | {count} |")
        lines.append("")
    else:
        lines.append("_No tags available._")
        lines.append("")
    lines.append("## Activity Timeline")
    lines.append("")
    month_counter: Dict[str, int] = defaultdict(int)
    for doc in docs:
        if doc.date:
            month_counter[doc.date[:7]] += 1
    if month_counter:
        lines.append("| Month | Documents |")
        lines.append("| --- | --- |")
        for month, count in sorted(month_counter.items(), reverse=True)[:18]:
            lines.append(f"| {month} | {count} |")
        lines.append("")
    else:
        lines.append("_No dated documents available._")
        lines.append("")
    lines.append("## Duplicate Section Hotspots")
    lines.append("")
    if not clusters:
        lines.append("No repeated sections detected across files.")
    else:
        lines.append(
            f"Detected {len(clusters)} repeated sections across {len(docs)} files. See `topic_overlaps.md` for details."
        )
    dest.write_text("\n".join(lines).rstrip() + "\n", encoding="utf-8")


def write_canonical_topics(
    clusters: List[Dict[str, object]], dest: Path, per_topic_limit: int = 5
) -> None:
    lines = ["# Canonical Topic Narratives", ""]
    lines.append(
        "Synthesized narratives derived from overlapping sections. Each entry "
        "identifies a canonical paragraph and references the original sources."
    )
    lines.append("")
    if not clusters:
        lines.append("No overlapping sections to consolidate.")
        dest.write_text("\n".join(lines).rstrip() + "\n", encoding="utf-8")
        return

    grouped: Dict[str, List[Dict[str, object]]] = defaultdict(list)
    for cluster in clusters:
        topic = cluster["occurrences"][0]["topic"]
        grouped[topic].append(cluster)

    for topic in sorted(grouped.keys()):
        lines.append(f"## {topic}")
        lines.append("")
        entries = grouped[topic][:per_topic_limit]
        for entry in entries:
            lines.append(f"### {entry['section_title']}")
            lines.append("")
            lines.append(f"> {entry['preview']}")
            lines.append("")
            lines.append("**Canonical source:**")
            primary = entry["occurrences"][0]
            lines.append(
                f"- `{primary['path']}` · {primary['doc_title']}"
            )
            if len(entry["occurrences"]) > 1:
                lines.append("")
                lines.append("**Additional references:**")
                for occurrence in entry["occurrences"][1:]:
                    lines.append(
                        f"- `{occurrence['path']}` · {occurrence['doc_title']}"
                    )
            lines.append("")
        lines.append("")
    dest.write_text("\n".join(lines).rstrip() + "\n", encoding="utf-8")


def build_report() -> None:
    docs = load_metadata()
    topic_counts = group_by_topic(docs)
    duplicates = find_duplicates(docs)
    lines = ["# Documentation Inventory Report", ""]
    lines.append("## Topic Coverage")
    lines.append("")
    lines.append("| Topic | Documents |")
    lines.append("| --- | --- |")
    for topic, items in sorted(topic_counts.items()):
        lines.append(f"| {topic} | {len(items)} |")
    lines.append("")
    lines.append("## Exact Duplicates (hash matches)")
    lines.append("")
    if duplicates:
        for digest, items in duplicates.items():
            lines.append(f"- `{digest[:12]}` → {len(items)} files")
            for doc in items:
                lines.append(f"  - `{doc.path.as_posix()}` ({doc.title})")
    else:
        lines.append("No duplicate files detected.")
    REPORT_FILE.write_text("\n".join(lines) + "\n", encoding="utf-8")
    print(f"Report written to {REPORT_FILE}")


def find_duplicates(docs: List[DocumentMetadata]) -> Dict[str, List[DocumentMetadata]]:
    grouped: Dict[str, List[DocumentMetadata]] = defaultdict(list)
    for doc in docs:
        grouped[doc.hash].append(doc)
    return {digest: items for digest, items in grouped.items() if len(items) > 1}


def main() -> None:
    parser = argparse.ArgumentParser(description="Documentation pipeline orchestrator")
    parser.add_argument("command", choices=["inventory", "report", "merge", "validate"])
    args = parser.parse_args()
    if args.command == "inventory":
        inventory()
    elif args.command == "report":
        build_report()
    elif args.command == "merge":
        merge_docs()
    else:
        validate_docs()


if __name__ == "__main__":
    main()

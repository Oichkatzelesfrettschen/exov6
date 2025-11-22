"""Utility helpers for documentation ingestion."""

from __future__ import annotations

import hashlib
import json
import re
import subprocess
from collections.abc import Iterable
from pathlib import Path
from typing import Dict, Iterable as TypingIterable, List, Optional, Sequence, Tuple

import frontmatter

from .models import SectionEntry

IGNORED_DIRS = {
    ".git",
    ".venv",
    "build",
    ".build",
    "docs/build",
    "docs/sphinx/build",
    "unified",
}

DATE_PATTERN = re.compile(r"(20\d{2})(?:[-_/\.](\d{2}))?(?:[-_/\.](\d{2}))?")
TOPIC_RULES: List[Tuple[str, Sequence[str]]] = [
    ("Temporal Sessions", ("session", "week", "log", "meeting")),
    ("Roadmaps & Plans", ("roadmap", "plan", "status", "scope", "execution", "task")),
    ("Standards & Compliance", ("standard", "posix", "susv", "compliance", "spec")),
    ("Architecture & Implementation", ("architecture", "design", "lock", "kernel", "libos", "capability")),
    ("Analyses & Audits", ("analysis", "audit", "report", "assessment")),
    ("Legacy Archive", ("archive", "legacy")),
    ("General & Misc", ()),
]


def iter_markdown_files(root: Path) -> TypingIterable[Path]:
    """Yield Markdown files under root, skipping ignored directories."""

    for path in root.rglob("*.md"):
        if any(part in IGNORED_DIRS for part in path.parts):
            continue
        yield path


def read_file(path: Path) -> str:
    return path.read_text(encoding="utf-8")


def extract_title(body: str, default: str) -> str:
    for line in body.splitlines():
        if line.strip().startswith("#"):
            return line.strip("# ").strip()
    pretty = default.replace("_", " ").replace("-", " ").title()
    return pretty or "Untitled"


def extract_headings(body: str) -> List[str]:
    headings: List[str] = []
    for line in body.splitlines():
        if line.startswith("#"):
            headings.append(line.strip())
    return headings


def extract_sections(body: str) -> List[SectionEntry]:
    sections: List[SectionEntry] = []
    current_title = "Introduction"
    buffer: List[str] = []

    def emit() -> None:
        nonlocal buffer, current_title
        text = "\n".join(buffer).strip()
        if text:
            sections.append(
                SectionEntry(
                    title=current_title,
                    text=text,
                    hash=compute_hash(normalize_block(text)),
                )
            )
        buffer = []

    for line in body.splitlines():
        if line.startswith("#"):
            emit()
            current_title = line.strip("# ").strip() or "Section"
        else:
            buffer.append(line)
    emit()
    return sections


def guess_date(path: Path, metadata: Dict[str, object]) -> Optional[str]:
    if "date" in metadata:
        raw = str(metadata["date"])
        return normalize_date(raw)
    match = DATE_PATTERN.search(path.as_posix())
    if match:
        year, month, day = match.groups()
        month = month or "01"
        day = day or "01"
        return f"{year}-{month}-{day}"
    git_date = git_last_date(path)
    return git_date


def normalize_date(value: str) -> Optional[str]:
    digits = re.findall(r"\d+", value)
    if not digits:
        return None
    if len(digits) >= 3:
        return f"{int(digits[0]):04d}-{int(digits[1]):02d}-{int(digits[2]):02d}"
    if len(digits) == 2:
        return f"{int(digits[0]):04d}-{int(digits[1]):02d}-01"
    year = digits[0]
    if len(year) == 4:
        return f"{year}-01-01"
    return None


def git_last_date(path: Path) -> Optional[str]:
    try:
        result = subprocess.run(
            ["git", "log", "-1", "--format=%ad", "--date=short", str(path)],
            capture_output=True,
            text=True,
            check=False,
        )
        value = result.stdout.strip()
        return value or None
    except FileNotFoundError:
        return None


def infer_topic(path: Path, title: str) -> str:
    haystack = f"{path.as_posix()} {title}".lower()
    for topic, keywords in TOPIC_RULES:
        if any(keyword in haystack for keyword in keywords):
            return topic
    return "General & Misc"


def compute_hash(body: str) -> str:
    return hashlib.sha256(body.encode("utf-8")).hexdigest()


def normalize_block(text: str) -> str:
    return " ".join(text.split())


def summarize_text(body: str, limit: int = 200) -> str:
    clean = " ".join(body.split())
    if len(clean) <= limit:
        return clean
    return clean[: limit - 3].rstrip() + "..."


def parse_document(path: Path) -> Tuple[Dict[str, object], str]:
    raw = read_file(path)
    try:
        parsed = frontmatter.loads(raw)
        metadata = parsed.metadata or {}
        body = parsed.content
    except Exception:
        metadata = {}
        body = raw
    return metadata, body


def dump_json(data: object, dest: Path) -> None:
    dest.write_text(json.dumps(data, indent=2, sort_keys=True), encoding="utf-8")


def load_json(path: Path) -> object:
    return json.loads(path.read_text(encoding="utf-8"))

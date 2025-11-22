"""Common data models for the documentation pipeline."""

from __future__ import annotations

from dataclasses import dataclass, field
from pathlib import Path
from typing import Dict, List, Optional


@dataclass(slots=True)
class SectionEntry:
    """Represents a normalized document section."""

    title: str
    text: str
    hash: str

    def to_dict(self) -> Dict[str, str]:
        return {"title": self.title, "text": self.text, "hash": self.hash}


@dataclass(slots=True)
class DocumentMetadata:
    """Normalized information about a Markdown document."""

    path: Path
    title: str
    date: Optional[str]
    topic: str
    tags: List[str]
    summary: str
    hash: str
    word_count: int
    headings: List[str]
    sections: List[SectionEntry]
    source: str = ""
    extra: Dict[str, str] = field(default_factory=dict)

    def to_dict(self) -> Dict[str, object]:
        return {
            "path": str(self.path),
            "title": self.title,
            "date": self.date,
            "topic": self.topic,
            "tags": self.tags,
            "summary": self.summary,
            "hash": self.hash,
            "word_count": self.word_count,
            "headings": self.headings,
            "sections": [section.to_dict() for section in self.sections],
            "source": self.source,
            "extra": self.extra,
        }


@dataclass(slots=True)
class TopicSummary:
    """Roll-up statistics for a topic grouping."""

    name: str
    count: int
    earliest: Optional[str]
    latest: Optional[str]
    files: List[Path]

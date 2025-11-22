# Gemini Agent Guide

Gemini assistants must ground every response in the canonical documentation:

1. Read `README.md` for architecture + workflow details.
2. Consult `docs/unified/roadmaps_and_plans.md` before summarizing plans.
3. Reference `docs/unified/topic_overlaps.md` when reconciling duplicated text.

## Execution Checklist

- Use the provided tooling (`python tools/run_docs_pipeline.py ...`, `make -C docs`).
- Never edit `archive/` unless explicitly tasked with historical work.
- When editing Markdown, normalize formatting via `mdformat`.
- Capture provenance: mention original file paths in summaries.

All outbound instructions should link back to `README.md` or the relevant
`docs/unified/` page so humans can verify the canonical context.

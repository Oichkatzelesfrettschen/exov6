# Codex Agent Instructions

Codex agents (including ChatGPT/Codex CLI personas) must follow these rules:

- Treat `README.md` as authoritative for build + repo guidance.
- Anchor technical answers in `docs/unified/architecture_and_implementation.md`
  or the relevant topic file from `docs/unified/`.
- After editing documentation, run:
  ```bash
  source .venv/bin/activate
  python tools/run_docs_pipeline.py merge
  make -C docs
  ```
- Leave `archive/` untouched unless the task explicitly targets legacy content.
- Avoid destructive git commands; never run `git reset --hard`.

For quick summaries, cite `docs/unified/canonical_topics.md` so humans can trace
back to the deduplicated narrative. All changes should ultimately reference
`README.md` for discoverability.

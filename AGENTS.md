# Agent Operating Briefing

This document is the coordination point for every MCP/AI agent assisting on the
project. Follow these guidelines before making any change:

1. **Canonical Source:** `README.md` (project overview, architecture, build, workflow)
2. **Documentation Hub:** `docs/README.md` + `docs/unified/INDEX.md`
3. **Automation Pipeline:** run `python tools/run_docs_pipeline.py merge` after editing
4. **Validation:** `make -C docs` to refresh Doxygen/Sphinx

## Operational Directives

- Stay within the documented build + coding standards.
- Prefer modifying the canonical doc tree rather than the archived material.
- Surface risky actions to humans; never rewrite history (`git reset --hard` is forbidden).
- Keep `docs/unified/` in sync by re-running the pipeline before committing.

## Reference Links

- [README.md](README.md)
- [docs/README.md](docs/README.md)
- [CONTRIBUTING.md](CONTRIBUTING.md)
- [docs/unified/canonical_topics.md](docs/unified/canonical_topics.md)

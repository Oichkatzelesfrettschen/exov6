# Claude Code Briefing

Claude agents should treat `README.md` as the single source of truth. When
implementing requests:

- Read `docs/unified/architecture_and_implementation.md` for subsystem context.
- Use the tooling stack defined in `docs/README.md` (`tools/run_docs_pipeline.py`, `make -C docs`).
- Keep edits deterministic—avoid speculative rewrites of archive files.
- After making documentation changes, run `python tools/run_docs_pipeline.py merge`
  and commit the refreshed `docs/unified/` outputs.

## Quick Reference

| Task | Command |
| --- | --- |
| Format Markdown | `mdformat <file>` |
| Rebuild docs | `make -C docs` |
| Merge documentation | `python tools/run_docs_pipeline.py merge` |
| Validate links | `bash scripts/validate_documentation_links.sh` |

Remember to reference `README.md` whenever providing instructions to humans or
other agents.***

# Contributing Guide

Welcome! To keep the repo consistent and reproducible:

1. **Start with `README.md`** – architecture, build instructions, coding standards.
2. **Use the docs pipeline** – after editing Markdown, run  
   `python tools/run_docs_pipeline.py merge` and commit the regenerated `docs/unified/`.
3. **Validate documentation** – `bash scripts/validate_documentation_links.sh` and `make -C docs`.
4. **Prefer incremental changes** – no force-pushes or history rewrites.
5. **Stay within supported toolchains** – clang/LLVM or GCC as described in `README.md`.

## Workflow Checklist

- Fork/branch, make focused commits.
- Run relevant tests/build targets.
- Include context in commit messages and reference source files in documentation updates.
- Open PRs against `main` with links to the updated sections of `docs/unified/`.

All contributors (human or AI) must cite `README.md` and the unified docs when
answering questions or summarizing work.

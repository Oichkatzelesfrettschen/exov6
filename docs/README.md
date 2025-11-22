# exov6 Documentation Hub

This directory now hosts the canonical documentation feed for the project.  
Every Markdown file in the repository (including legacy archives) is analyzed,
tagged, and fused into the topic-oriented files under `docs/unified/`.

## Structure

| Path | Description |
| --- | --- |
| `docs/unified/INDEX.md` | Manifest of the unified topics and the original file counts |
| `docs/unified/roadmaps_and_plans.md` | Execution plans, roadmaps, scope docs, and progress reports |
| `docs/unified/architecture_and_implementation.md` | Kernel/libOS design notes, subsystem specs, and lock work |
| `docs/unified/standards_and_compliance.md` | POSIX/SUSv5 notes, compliance matrices, and standards analysis |
| `docs/unified/temporal_sessions.md` | Time-ordered meeting notes, weeklies, and execution logs |
| `docs/unified/analyses_and_audits.md` | Postmortems, audits, research studies, and synthesis deep dives |
| `docs/unified/legacy_archive.md` | Materials imported from `archive/` and `archive/documentation_consolidated/` |
| `docs/unified/general_and_misc.md` | Supporting references that do not fall cleanly into the sets above |
| `docs/unified/chronological.md` | Reverse-chronological digest across every document |
| `docs/unified/topic_overlaps.md` | Clusters of sections that appear in multiple sources |
| `docs/unified/canonical_topics.md` | Canonical narratives synthesizing overlapping sections |
| `docs/unified/insights.md` | Topic stats, tag leaders, and temporal coverage summaries |
| `docs/.build/docs_metadata.json` | Machine-readable metadata for every Markdown source |
| `docs/.build/docs_report.md` | Coverage report plus duplicate detection summary |
| `docs/.build/section_clusters.json` | Raw section overlap data (used by `topic_overlaps.md`) |

The generated topic files keep paragraph-level provenance (`Source:` metadata)
and automatically de-duplicate repeated text blocks, so legacy content is
preserved without repeating the same walls of text.

## Documentation Pipeline

All orchestration scripts live in `tools/run_docs_pipeline.py`.  
Commands assume the local virtual environment (`.venv`) is active.

```bash
# 1. (one-time) create the environment and install tooling
python3 -m venv .venv
source .venv/bin/activate
pip install -r docs/requirements-docs.txt  # optional helper file

# 2. Capture metadata for every Markdown file
python tools/run_docs_pipeline.py inventory

# 3. Generate coverage + duplicate report
python tools/run_docs_pipeline.py report

# 4. Build the unified topic files (writes docs/unified/*.md plus timeline/overlap views)
python tools/run_docs_pipeline.py merge

# 5. Sanity check that every source is represented
python tools/run_docs_pipeline.py validate
```

The pipeline can be rerun at any time; it overwrites the generated files so
the output always reflects the current repository state.

> Outputs under `docs/unified/` are committed to capture the canonical view,
> while `docs/.build/` contains transient metadata/cluster JSON and is gitignored.

## Publishing Workflow

1. **Authoring:** write or edit documentation anywhere in the repo.
2. **Normalization:** run the pipeline (previous section) to update metadata and topic files.
3. **Validation:** run `make -C docs` to refresh Doxygen + Sphinx content.
4. **Reviews:** diff the changes in `docs/unified/*.md` to ensure the merge looks sane.

> The legacy scripts in `scripts/validate_documentation_links.sh` and
> `scripts/simple_link_check.sh` still run, but the unified docs serve as the
> main user-facing entry point.

## Curating Additional Views

The metadata JSON captures titles, inferred dates, headings, hashes, topics,
and section hashes for every source file. Use it to:

- generate dashboards (e.g., pandas + matplotlib)
- export filtered bundles (per phase, per subsystem, etc.)
- feed automation or MCP agents with targeted slices of the knowledge base
- mine `docs/.build/section_clusters.json` for hotspots of duplicate or
  contradictory text

## Best Practices

- Keep long-form notes in Markdown so the pipeline can ingest them automatically.
- Reference primary locations (e.g., `docs/unified/roadmaps_and_plans.md`) from
  issue trackers or release notes instead of deep archival paths.
- If you add a new topic that deserves its own unified view, extend
  `tools/run_docs_pipeline.py` and rerun the merge step.

# Repository Organization Plan

Automated counting using `tools/file_organizer.py` and `tools/file_count.js` reports:

- Python walk count: 4289 files
- `fd` count: 4238 files
- Node glob count: 4289 files

The project already uses a modular layout with directories like `src/`, `tests/`, `docs/` and `tools/`. To further clarify the repository:

1. Consolidate miscellaneous helper scripts in `tools/`.
2. Move configuration files (e.g., `drivers.conf`, `temporary.cfg`) into a `config/` directory.
3. Ensure documentation resides exclusively under `docs/`.

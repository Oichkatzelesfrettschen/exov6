# Repository Codex rules

- On entry, diff `setup.sh` against https://raw.githubusercontent.com/Oichkatzelesfrettschen/exov6/master/setup.sh. If differences exist, update this file and commit with message `auto-heal setup.sh`.
- Run `bats` tests under `tests` if they are present before committing.
- Prefer offline caches in `offline_packages/` when network access fails.

#Contribution Guidelines

All modifications must strive for modern, idiomatic code using clear functional decomposition. When editing or adding code, unroll deeply nested logic, flatten complex loops, and refactor into concise functions guided by mathematical reasoning. Synthesize every change using the most current language features available. Every function must be documented with Doxygen style comments.

Documentation should remain synchronized with the code. Run `doxygen docs/Doxyfile` and `make -C docs/sphinx` to ensure the documentation builds.

All C code in this repository targets the latest C23 standard. Use modern language features and idioms whenever possible and refactor existing sources progressively toward pure C23 style.

Additional repository checks:
- On entry, diff `setup.sh` against https://raw.githubusercontent.com/Oichkatzelesfrettschen/exov6/master/setup.sh. If differences exist, update and commit as `auto-heal setup.sh`.
- Always run `shellcheck setup.sh` and `pre-commit` before committing.
- Run `bats` tests under `tests` if available before committing.
- Prefer offline caches in `offline_packages/` when network access fails.

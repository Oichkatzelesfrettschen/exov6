#Contribution Guidelines

All modifications must strive for modern, idiomatic code using clear functional decomposition. When editing or adding code, unroll deeply nested logic, flatten complex loops, and refactor into concise functions guided by mathematical reasoning. Synthesize every change using the most current language features available. Every function must be documented with Doxygen style comments.

Documentation should remain synchronized with the code. Run `doxygen docs/Doxyfile` and `make -C docs/sphinx` to ensure the documentation builds.

All C code in this repository targets the latest C23 standard. Use modern
language features and idioms whenever possible and refactor existing sources
progressively toward pure C23 style.

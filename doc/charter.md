# Phoenix Exokernel Project Charter

## Goals
- Provide a minimal kernel that exposes hardware capabilities directly to user space.
- Build a libOS and userland components on top of these primitives.
- Encourage experimentation with novel OS abstractions.

## Contributor Guidelines
- Follow the coding standards described in `CONTRIBUTING.md`.
- Run `pre-commit` before submitting patches.
- Discuss large changes on the mailing list or issue tracker first.
- Document new features and tests.

## Governance Model
- Development is open to the community.
- Patches are reviewed by maintainers before merging.
- Decisions are made by consensus when possible; maintainers provide final guidance when disagreements arise.
- Philosophical technical debt is tracked in `doc/ptd_log.md`.

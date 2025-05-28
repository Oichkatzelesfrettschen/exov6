# Phoenix Exokernel Charter

This document describes the guiding principles of the Phoenix exokernel
project. It outlines the long term goals, how contributors can
participate, and the basic governance model used to steer development.

## Goals

- Build a small, capability based exokernel that exposes hardware
  resources directly to user space.
- Provide a flexible libOS that implements POSIX, BSD and SVR4
  personalities without enlarging the kernel.
- Encourage experimentation with scheduling models, typed channels and
  user space drivers.
- Keep the core code understandable so new contributors can explore the
  system with minimal friction.

## Contributor Guidelines

Contributions are welcome from anyone. To keep patches manageable,
please follow these simple rules:

1. Keep commits focused on a single change and include clear commit
   messages.
2. Discuss larger features on the mailing list or issue tracker before
   implementation.
3. Documentation updates are just as valuable as code and are strongly
   encouraged.

## Governance Model

Phoenix is maintained by a small group of volunteers. Design decisions
are reached by consensus on the public mailing list. In case of
conflict, the maintainers listed in `MAINTAINERS` have final say.
Releases are cut periodically once the test suite passes and planned
features are stable. Everyone is invited to participate in reviews and
planning.

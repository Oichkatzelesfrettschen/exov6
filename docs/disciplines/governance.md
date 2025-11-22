# Governance and RFC Process

## Overview
Major changes to the Phoenix Exokernel architecture or public APIs must go through a Request for Comments (RFC) process. This ensures transparency, community review, and high-quality design.

## RFC Process

1.  **Idea**: Start a discussion in the developer channels.
2.  **Draft**: Write a design document in `docs/rfcs/`. Use the template `0000-template.md`.
    *   Title, Author, Status
    *   Summary
    *   Motivation
    *   Detailed Design
    *   Alternatives Considered
3.  **Review**: Submit a Pull Request. Core maintainers and the community review the design.
4.  **Approval**: Once approved, the RFC is merged and assigned a number (e.g., `0001-pqc-integration.md`).
5.  **Implementation**: Coding begins.

## Decision Making
*   **Consensus**: We strive for consensus among core maintainers.
*   **Benevolent Dictator**: In case of deadlocks, the project lead has the final say (rare).

## Breaking Changes
Any breaking change (MAJOR version bump) **requires** an approved RFC.

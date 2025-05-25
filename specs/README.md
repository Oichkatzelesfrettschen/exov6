# TLA+ Specifications

This directory contains TLA+ models for Exo.

## Running the model checker

Install the TLA+ tools and ensure `tlc` is on your `PATH`. To check the
capability life cycle model run:

```bash
cd specs
tlc CapabilityLifecycle.tla
```

The checker explores the state space defined in `CapabilityLifecycle.tla` and
reports any invariant violations.

# TLA+ Models

This directory contains specifications used to explore the capability
lifecycle and arbitration rules in ExO.

## Running the Model Checker

TLA+ tooling is distributed as part of the [TLA Toolbox](https://github.com/tlaplus/tlaplus).
After installing the `tla2tools.jar` package, the model can be checked via:

```bash
java -jar /path/to/tla2tools.jar Capability.tla
```

The default specification defines a constant set of `Users` and verifies
`ActiveInv`, which ensures that the current active capability is always
part of the allocated set.

## C Reference Model

For easier experimentation, `c/capability_model.c` provides a small C
translation of `Capability.tla`. The state machine mirrors the TLA+
transitions (`Create`, `Revoke`, and `YieldTo`) and exposes a simple
API that can be embedded in unit tests or further model checking tools.
Compile with `-DCAPABILITY_MODEL_DEMO` to see a short demonstration.

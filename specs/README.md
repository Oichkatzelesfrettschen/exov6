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

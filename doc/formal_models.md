# Working with Formal Models

The `formal/` directory houses small Coq developments. TLA+
specifications reside under `formal/specs/tla/`. Contributors can extend these
models to capture new behaviour or prove additional properties.

## Building

```
make -C formal/coq
```

compiles the Coq files. The TLA+ specs can be explored with the
`tlc` model checker:

```
tlc formal/specs/tla/ExoCap.tla
```

Both tools are optional. The build will skip these steps if the
commands are unavailable.

## Extending the Models

- Place new Coq modules under `formal/coq/` and list them in
  `formal/coq/_CoqProject`.
- Add new TLA+ modules under `formal/specs/tla/` and reference them in
  the documentation or tests as needed.

Formal models should remain lightweight and easy to build so they can
run as part of the continuous integration tests.

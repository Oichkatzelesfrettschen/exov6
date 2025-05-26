# Formal Models

This directory collects formal specifications of selected subsystem APIs.

- `coq/` contains Coq proofs.
- `tla/` contains TLA+ specifications checked with `tlc`.

Run `make -C formal/coq` to type-check the Coq development. To model
check the TLA+ specs run `tlc formal/tla/ExoCap.tla` if the `tlc`
command is available.

New `.v` or `.tla` files can be added to extend the models. Update
`formal/coq/_CoqProject` when adding new Coq modules.

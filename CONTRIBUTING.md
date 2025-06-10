# Contributing

To run formatting and static analysis checks automatically on commit, this repository uses `pre-commit` hooks. If `pre-commit` is not already installed, you can get it via `pip`:

```sh
pip install pre-commit
```

Once installed, set up the hooks with the configuration in
`.pre-commit-config.yaml` using:

```sh
pre-commit install
```

You can also run all checks manually with:

```sh
pre-commit run --all-files
```


Formal models describing parts of the system live under the `formal/`
directory. See `doc/formal_models.md` for instructions on building and
extending these models.

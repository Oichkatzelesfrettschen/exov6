# Contributing

To run formatting and static analysis checks automatically on commit, this repository uses `pre-commit` hooks. If `pre-commit` is not already installed, you can get it via `pip`:

```sh
pip install pre-commit
```

Once installed, set up the hooks with:

```sh
pre-commit install
```

You can also run all checks manually with:

```sh
pre-commit run --all-files
```


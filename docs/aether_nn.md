# Aether Neural Network Library

This library provides a compact neural-network toolkit designed for
real-time heuristics within ExoV6. It offers:

- Arena-based memory management for deterministic allocation.
- Embedding layers with composable aggregation strategies.
- Dense layers with SGD, momentum, or Adam optimizers.
- Optional int8 quantized inference for low-memory deployments.

The module is intended for integration with kernel and LibOS components,
including the unified lock predictor and resurrection DAG. See
`include/aether_nn.h` for the public API.

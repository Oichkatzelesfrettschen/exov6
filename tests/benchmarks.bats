#!/usr/bin/env bats

@test "lattice vs pipe benchmark" {
  make -C tests/microbench lattice_pipe_bench >/dev/null
  run tests/microbench/lattice_pipe_bench
  [ "$status" -eq 0 ]
}

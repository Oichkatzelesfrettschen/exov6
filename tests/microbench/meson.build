bench_src = files('cap_verify_bench.c',
                  'exo_yield_to_bench.c',
                  'proc_cap_test.c',
                  'lattice_pipe_bench.c')
foreach src : bench_src
  exe_name = src.stem()
  executable(exe_name, src,
             include_directories: include_directories('../../include'),
             install: false)
endforeach

bench_src = files('cap_verify_bench.c',
                  'exo_yield_to_bench.c',
                  'proc_cap_test.c')
foreach src : bench_src
  exe_name = src.stem()
  executable(exe_name, src,
             include_directories: include_directories('../../libos/include',
                                                     '../../include'),
             install: false)
endforeach

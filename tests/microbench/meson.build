inc = include_directories('../../libos/include', '../../src-headers')

executable('cap_verify_bench', 'cap_verify_bench.c',
           include_directories: inc,
           install: false)

executable('exo_yield_to_bench', 'exo_yield_to_bench.c',
           include_directories: inc,
           install: false)

executable('proc_cap_test',
           ['proc_cap_test.c', '../../libos/procwrap.c', '../../libos/capwrap.c'],
           include_directories: inc,
           install: false)

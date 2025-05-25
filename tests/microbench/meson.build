incdir = include_directories('../../libos/include', '../../src-headers')

microbench_common = static_library(
    'microbench_common',
    '../../libos/procwrap.c',
    '../../libos/capwrap.c',
    include_directories: incdir,
    pic: false,
)

cap_verify_bench = executable('cap_verify_bench', 'cap_verify_bench.c',
    include_directories: incdir,
    link_with: microbench_common,
    install: false)

exo_yield_to_bench = executable('exo_yield_to_bench', 'exo_yield_to_bench.c',
    include_directories: incdir,
    link_with: microbench_common,
    install: false)

proc_cap_test = executable('proc_cap_test', 'proc_cap_test.c',
    include_directories: incdir,
    link_with: microbench_common,
    install: false)

run_cmd = ' && '.join([
    join_paths(meson.current_build_dir(), 'cap_verify_bench'),
    join_paths(meson.current_build_dir(), 'exo_yield_to_bench'),
    join_paths(meson.current_build_dir(), 'proc_cap_test')
])

run_target('microbench-run',
    command: ['sh', '-c', run_cmd],
    depends: [cap_verify_bench, exo_yield_to_bench, proc_cap_test])

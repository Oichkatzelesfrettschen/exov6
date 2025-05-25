project('xv6', 'c', default_options: ['c_std=c23'])

clang_tidy = find_program('clang-tidy', required: false)

src_dirs = ['src-kernel', 'src-uland', 'src-uland/user', 'libos']

sources = []
foreach d : src_dirs
  sources += files(d + '/*.c')
endforeach

executable('kernel', sources,
           include_directories: include_directories('.',
                                            'src-headers',
                                            'src-kernel/include',
                                            'proto'),
           install: false)

if clang_tidy.found()
  run_target('clang-tidy', command: [clang_tidy, sources],
             depends: sources)
endif

subdir('libnstr_graph')

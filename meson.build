project('xv6', 'c', default_options: ['c_std=c23'])

clang_tidy = find_program('clang-tidy', required: false)
bison = find_program('bison', required : false)

src_dirs = ['src-kernel', 'src-uland', 'src-uland/user', 'libos']

sources = []
foreach d : src_dirs
  sources += files(d + '/*.c')
endforeach

executable('kernel', sources,
           include_directories: include_directories('.',
                                            'src-headers',
                                            'src-kernel/include',
                                            'proto',
                                            'libos/include'),
           install: false)

if clang_tidy.found()
  run_target('clang-tidy', command: [clang_tidy, sources],
             depends: sources)
endif

if bison.found()
  # Sample grammar rule for future .y files
  # sample = custom_target('sample.tab.c',
  #   command: [bison, '-d', '@INPUT@'],
  #   input: 'path/to/sample.y',
  #   output: ['sample.tab.c', 'sample.tab.h'])
endif

subdir('libnstr_graph')

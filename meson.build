project('xv6', 'c', default_options: ['c_std=c23'])

option('config_smp', type: 'boolean', value: true, description: 'enable SMP spinlocks')

clang_tidy = find_program('clang-tidy', required: false)

src_dirs = ['src-kernel', 'src-uland', 'libos']

sources = []
foreach d : src_dirs
  sources += files(d + '/*.c')
endforeach

if not get_option('config_smp')
  sources -= files('src-kernel/spinlock.c',
                   'src-kernel/qspinlock.c',
                   'src-kernel/rspinlock.c')
endif

executable('kernel', sources,
           c_args: ['-DCONFIG_SMP=' + (get_option('config_smp') ? '1' : '0')],
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

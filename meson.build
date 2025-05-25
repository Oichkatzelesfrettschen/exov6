project('xv6', 'c', default_options: ['c_std=c23'])

clang_tidy = find_program('clang-tidy', required: false)

src_dirs = ['src-kernel', 'src-uland', 'src-uland/user', 'libos']

sources = []
foreach d : src_dirs
  sources += files(d + '/*.c')
endforeach

kernel = executable('kernel', sources,
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

qemu = find_program('qemu-system-x86_64', 'qemu-system-i386', 'qemu', required: false)
if qemu.found()
  run_target('qemu-nox',
             command: [qemu, '-nographic', '-serial', 'stdio',
                       '-kernel', kernel.full_path()],
             depends: kernel,
             console: true)
endif

subdir('libnstr_graph')

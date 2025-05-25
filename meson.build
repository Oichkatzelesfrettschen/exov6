project('xv6', 'c', default_options: ['c_std=c23'])
add_project_arguments('-Wall', '-Werror', language: ['c', 'cpp'])

use_ticket_lock = get_option('use_ticket_lock')
common_cargs = []
if use_ticket_lock
  common_cargs += ['-DUSE_TICKET_LOCK']
endif

clang_tidy = find_program('clang-tidy', required: false)
bison = find_program('bison', required: false)
if bison.found()
  example_parser = custom_target('example_parser',
    input: 'proto/example.y',
    output: ['example_parser.c', 'example_parser.h'],
    command: [bison, '--defines=@OUTPUT1@', '-o', '@OUTPUT0@', '@INPUT@'])
endif

# User-space runtime library
mock_capnpc = find_program('scripts/mock_capnpc.sh')
driver_capnp = custom_target('driver_capnp',
    input: 'proto/driver.capnp',
    output: ['driver.capnp.c', 'driver.capnp.h'],
    command: [mock_capnpc, '@INPUT@'])

libos_sources = [
  'src-uland/ulib.c',
  'src-uland/printf.c',
  'src-uland/umalloc.c',
  'src-uland/caplib.c',
  'src-uland/chan.c',
  'src-uland/door.c',
  driver_capnp,
  'src-uland/math_core.c',
  'src-uland/libos/sched.c',
  'libos/fs.c',
  'libos/file.c',
  'libos/driver.c',
  'libos/affine_runtime.c',
  'libos/posix.c',
  'libos/capnp/capnp_helpers.c',
]

libos = static_library('libos', libos_sources,
    include_directories: include_directories('.', 'src-headers', 'proto', 'libos/include', 'libos/capnp'),
    c_args: common_cargs)

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
                                            'libos/include',
                                            'libos/capnp'),
           install: false,
           c_args: common_cargs)

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

# User-space programs
uprogs = {
  'cat': 'src-uland/cat.c',
  'echo': 'src-uland/echo.c',
  'forktest': 'src-uland/forktest.c',
  'grep': 'src-uland/grep.c',
  'init': 'src-uland/init.c',
  'kill': 'src-uland/kill.c',
  'ln': 'src-uland/ln.c',
  'ls': 'src-uland/ls.c',
  'mkdir': 'src-uland/mkdir.c',
  'rm': 'src-uland/rm.c',
  'sh': 'src-uland/sh.c',
  'stressfs': 'src-uland/stressfs.c',
  'usertests': 'src-uland/usertests.c',
  'wc': 'src-uland/wc.c',
  'zombie': 'src-uland/zombie.c',
  'phi': 'src-uland/phi.c',
  'exo_stream_demo': 'src-uland/user/exo_stream_demo.c',
  'dag_demo': 'src-uland/user/dag_demo.c',
  'beatty_demo': 'src-uland/user/beatty_demo.c',
  'beatty_dag_demo': 'src-uland/user/beatty_dag_demo.c',
  'ipc_test': 'src-uland/ipc_test.c',
  'nbtest': 'src-uland/nbtest.c',
  'rcrs': 'src-uland/rcrs.c',
  'pingdriver': 'src-uland/pingdriver.c',
  'typed_chan_demo': 'src-uland/user/typed_chan_demo.c',
  'typed_chan_send': 'src-uland/user/typed_chan_send.c',
  'typed_chan_recv': 'src-uland/user/typed_chan_recv.c',
  'affine_channel_demo': 'src-uland/user/affine_channel_demo.c',
  'chan_dag_supervisor_demo': 'src-uland/user/chan_dag_supervisor_demo.c',
  'chan_beatty_rcrs_demo': 'src-uland/user/chan_beatty_rcrs_demo.c',
  'libos_posix_test': 'src-uland/libos_posix_test.c',
  'libos_posix_extra_test': 'src-uland/user/libos_posix_extra_test.c',
  'qspin_demo': 'src-uland/user/qspin_demo.c',
  'tty_demo': 'src-uland/tty_demo.c',
}

uprogs_targets = []
foreach name, path : uprogs
  exe = executable('_' + name, path,
                   include_directories: include_directories('.', 'src-headers', 'proto', 'libos/include', 'libos/capnp'),
                   link_with: libos,
                   install: false,
                   c_args: common_cargs)
  uprogs_targets += exe
endforeach

# mkfs and filesystem image
mkfs = executable('mkfs', 'mkfs.c', install: false)
fsimg = custom_target('fs.img',
  output: 'fs.img',
  command: [mkfs, '@OUTPUT@', 'README'] + uprogs_targets,
  depends: uprogs_targets,
  build_by_default: true)

subdir('tests/microbench')

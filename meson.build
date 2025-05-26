project('xv6', 'c', default_options: ['c_std=c23'])
add_project_arguments('-Wall', '-Werror', language: ['c', 'cpp'])

use_ticket_lock = get_option('use_ticket_lock')
ipc_debug = get_option('ipc_debug')
use_capnp = get_option('use_capnp')
use_simd = get_option('use_simd')
common_cargs = []
if use_ticket_lock
  common_cargs += ['-DUSE_TICKET_LOCK']
endif
if ipc_debug
  common_cargs += ['-DIPC_DEBUG']
endif
cc = meson.get_compiler('c')
if cc.has_argument('-mdecimal-float')
  common_cargs += ['-mdecimal-float', '-DHAVE_DECIMAL_FLOAT']
if use_simd
  common_cargs += ['-DUSE_SIMD']
endif

clang_tidy = find_program('clang-tidy', required: false)
bison = find_program('bison', required: false)
if bison.found()
  example_parser = custom_target('example_parser',
    input: 'engine/proto/example.y',
    output: ['example_parser.c', 'example_parser.h'],
    command: [bison, '--defines=@OUTPUT1@', '-o', '@OUTPUT0@', '@INPUT@'])
endif

# User-space runtime library
mock_capnpc = find_program('scripts/mock_capnpc.sh')
capnp_targets = []
if use_capnp
  driver_capnp = custom_target('driver_capnp',
      input: 'engine/proto/driver.capnp',
      output: ['driver.capnp.c', 'driver.capnp.h'],
      command: [mock_capnpc, '@INPUT@'])
  hello_capnp = custom_target('hello_capnp',
      input: 'engine/proto/hello.capnp',
      output: ['hello.capnp.c', 'hello.capnp.h'],
      command: [mock_capnpc, '@INPUT@'])
  capnp_targets += [driver_capnp, hello_capnp]
  libcapnp = static_library('libcapnp',
      ['engine/libos/capnp/capnp_helpers.c'] + capnp_targets,
      include_directories: include_directories('.', 'engine/include', 'engine/proto', 'engine/libos/capnp'),
      c_args: common_cargs)
endif

libos_sources = [
  'engine/user/ulib.c',
  'engine/user/printf.c',
  'engine/user/umalloc.c',
  'engine/user/caplib.c',
  'engine/user/chan.c',
  'engine/user/door.c',
  'engine/user/math_core.c',
  'engine/user/libos/sched.c',
  'engine/libos/fs.c',
  'engine/libos/file.c',
  'engine/libos/driver.c',
  'engine/libos/affine_runtime.c',
  'engine/libos/env.c',
  'engine/libos/ipc.c',
  'engine/libos/posix.c',
  'engine/libos/termios.c',
  'engine/libos/microkernel/cap.c',
  'engine/libos/microkernel/msg_router.c',
  'engine/libos/microkernel/resource_account.c',
  'engine/libos/microkernel/registration.c',
]

libos = static_library('libos', libos_sources,
    include_directories: include_directories('.', 'engine/include', 'engine/proto', 'engine/libos/include', 'engine/libos/capnp'),
    c_args: common_cargs)

src_dirs = ['kernel/hypervisor', 'engine/kernel', 'engine/user', 'engine/user/user', 'engine/libos']

sources = []
foreach d : src_dirs
  sources += files(d + '/*.c')
endforeach
sources += files('engine/kernel/runqueue.c')

kernel = executable('kernel', sources,
           include_directories: include_directories('.',
                                            'engine/include',
                                            'engine/kernel/include',
                                            'kernel/hypervisor',
                                            'engine/proto',
                                            'engine/libos/include',
                                            'engine/libos/capnp'),
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
  'cat': 'engine/user/cat.c',
  'echo': 'engine/user/echo.c',
  'forktest': 'engine/user/forktest.c',
  'grep': 'engine/user/grep.c',
  'init': 'engine/user/init.c',
  'kill': 'engine/user/kill.c',
  'ln': 'engine/user/ln.c',
  'ls': 'engine/user/ls.c',
  'mkdir': 'engine/user/mkdir.c',
  'rm': 'engine/user/rm.c',
  'sh': 'engine/user/sh.c',
  'stressfs': 'engine/user/stressfs.c',
  'usertests': 'engine/user/usertests.c',
  'wc': 'engine/user/wc.c',
  'zombie': 'engine/user/zombie.c',
  'phi': 'engine/user/phi.c',
  'exo_stream_demo': 'engine/user/user/exo_stream_demo.c',
  'dag_demo': 'engine/user/user/dag_demo.c',
  'beatty_demo': 'engine/user/user/beatty_demo.c',
  'beatty_dag_demo': 'engine/user/user/beatty_dag_demo.c',
  'ipc_test': 'engine/user/ipc_test.c',
  'nbtest': 'engine/user/nbtest.c',
  'rcrs': 'engine/user/rcrs.c',
  'libos_posix_test': 'engine/user/libos_posix_test.c',
  'libos_posix_extra_test': 'engine/user/user/libos_posix_extra_test.c',
  'qspin_demo': 'engine/user/user/qspin_demo.c',
  'tty_demo': 'engine/user/tty_demo.c',
  'termios_demo': 'engine/user/termios_demo.c',
  'msgqueue_demo': 'demos/examples/msgqueue_demo.c',
  'fib_big_demo': 'demos/examples/fib_big_demo.c',
  'start_guest': 'engine/user/start_guest.c',
}

if use_capnp
  uprogs += {
    'pingdriver': 'engine/user/pingdriver.c',
    'typed_chan_demo': 'engine/user/user/typed_chan_demo.c',
    'typed_chan_send': 'engine/user/user/typed_chan_send.c',
    'typed_chan_recv': 'engine/user/user/typed_chan_recv.c',
    'affine_channel_demo': 'engine/user/user/affine_channel_demo.c',
    'chan_dag_supervisor_demo': 'engine/user/user/chan_dag_supervisor_demo.c',
    'chan_beatty_rcrs_demo': 'engine/user/user/chan_beatty_rcrs_demo.c',
  }
endif

uprogs_targets = []
foreach name, path : uprogs
  incs = [include_directories('.', 'engine/include', 'engine/proto', 'engine/libos/include')]
  deps = [libos]
  if use_capnp
    incs += include_directories('engine/libos/capnp')
    deps += libcapnp
  endif
  exe = executable('_' + name, path,
                   include_directories: incs,
                   link_with: deps,
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
subdir('tests/posix')

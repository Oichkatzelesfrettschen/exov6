project('xv6', 'c')
cc = meson.get_compiler('c')
std_flag = ''
if cc.has_argument('-std=c23')
  std_flag = '-std=c23'
elif cc.has_argument('-std=c2x')
  std_flag = '-std=c2x'
endif
if std_flag != ''
  add_project_arguments(std_flag, language: 'c')
endif
add_project_arguments('-Wall', '-Werror', language: ['c', 'cpp'])

use_ticket_lock = get_option('use_ticket_lock')
ipc_debug = get_option('ipc_debug')
use_capnp = get_option('use_capnp')
use_simd = get_option('use_simd')
mcu = get_option('mcu')
common_cargs = []
if use_ticket_lock
  common_cargs += ['-DUSE_TICKET_LOCK']
endif
if ipc_debug
  common_cargs += ['-DIPC_DEBUG']
endif
if cc.has_argument('-mdecimal-float')
  common_cargs += ['-mdecimal-float', '-DHAVE_DECIMAL_FLOAT']
endif
if use_simd
  common_cargs += ['-DUSE_SIMD']
endif
if mcu
  common_cargs += ["-DMCU"]
endif

if mcu
  kernel = executable('kernel', ['src/arch/mcu/startup.c', 'kernel/picokernel.c', 'user/blink.c'],
      include_directories: include_directories('.', 'include', 'src', 'src/arch/mcu'),
      install: false,
      c_args: common_cargs)
  subdir_done()
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
capnp_targets = []
if use_capnp
  driver_capnp = custom_target('driver_capnp',
      input: 'proto/driver.capnp',
      output: ['driver.capnp.c', 'driver.capnp.h'],
      command: [mock_capnpc, '@INPUT@'])
  hello_capnp = custom_target('hello_capnp',
      input: 'proto/hello.capnp',
      output: ['hello.capnp.c', 'hello.capnp.h'],
      command: [mock_capnpc, '@INPUT@'])
  capnp_targets += [driver_capnp, hello_capnp]
  libcapnp = static_library('libcapnp',
      ['libos/capnp/capnp_helpers.c'] + capnp_targets,
      include_directories: include_directories('.', 'include', 'proto', 'libos/capnp'),
      c_args: common_cargs)
endif

libos_sources = [
  'user/ulib.c',
  'user/printf.c',
  'user/umalloc.c',
  'user/caplib.c',
  'user/chan.c',
  'user/door.c',
  'user/math_core.c',
  'user/libos/sched.c',
  'libos/fs.c',
  'libos/file.c',
  'libos/driver.c',
  'libos/affine_runtime.c',
  'libos/env.c',
  'libos/ipc.c',
  'libos/posix.c',
  'libos/termios.c',
  'libos/microkernel/cap.c',
  'libos/microkernel/msg_router.c',
  'libos/microkernel/resource_account.c',
  'libos/microkernel/registration.c',
]

libos = static_library('libos', libos_sources,
    include_directories: include_directories('.', 'include', 'proto', 'libos/capnp'),
    c_args: common_cargs)

src_dirs = [
  'kernel/hypervisor',
  'kernel',
  'user',
  'demos',
  'libos',
  'userspace/libposix',
  'userspace/libbaremetal',
  'userspace/lib9p',
  'userspace/stubs',
  'src/arch/generic',
  'src/arch/x86/legacy',
  'src/arch/x86/modern',
]

sources = []
foreach d : src_dirs
  sources += files(d + '/*.c')
endforeach

kernel = executable('kernel', sources,
           include_directories: include_directories('.',
                                            'include',
                                            'kernel/include',
                                           'kernel/hypervisor',
                                            'proto',
                                            'libos/capnp',
                                            'userspace/stubs',
                                            'src',
                                            'src/arch/x86/legacy',
                                            'src/arch/x86/modern'),
           install: false,
           c_args: common_cargs,
           link_with: [libddekit])

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

subdir('src/ddekit')
subdir('src/libnstr_graph')

# User-space programs
uprogs = {
  'cat': 'user/cat.c',
  'echo': 'user/echo.c',
  'forktest': 'user/forktest.c',
  'grep': 'user/grep.c',
  'init': 'user/init.c',
  'kill': 'user/kill.c',
  'ln': 'user/ln.c',
  'ls': 'user/ls.c',
  'mkdir': 'user/mkdir.c',
  'rm': 'user/rm.c',
  'sh': 'user/sh.c',
  'stressfs': 'user/stressfs.c',
  'usertests': 'user/usertests.c',
  'wc': 'user/wc.c',
  'zombie': 'user/zombie.c',
  'phi': 'user/phi.c',
  'exo_stream_demo': 'demos/exo_stream_demo.c',
  'dag_demo': 'demos/dag_demo.c',
  'beatty_demo': 'demos/beatty_demo.c',
  'beatty_dag_demo': 'demos/beatty_dag_demo.c',
  'ipc_test': 'user/ipc_test.c',
  'nbtest': 'user/nbtest.c',
  'fileserver': 'user/fileserver.c',
  'rcrs': 'user/rcrs.c',
  'libos_posix_test': 'user/libos_posix_test.c',
  'libos_posix_extra_test': 'demos/libos_posix_extra_test.c',
  'qspin_demo': 'demos/qspin_demo.c',
  'tty_demo': 'user/tty_demo.c',
  'termios_demo': 'user/termios_demo.c',
  'msgqueue_demo': 'demos/msgqueue_demo.c',
  'fib_big_demo': 'demos/fib_big_demo.c',
  'start_guest': 'user/start_guest.c',
  'hv_demo': 'demos/hv_demo.c',
}

if use_capnp
  uprogs += {
    'pingdriver': 'user/pingdriver.c',
    'typed_chan_demo': 'demos/typed_chan_demo.c',
    'typed_chan_send': 'demos/typed_chan_send.c',
    'typed_chan_recv': 'demos/typed_chan_recv.c',
    'affine_channel_demo': 'demos/affine_channel_demo.c',
    'chan_dag_supervisor_demo': 'demos/chan_dag_supervisor_demo.c',
    'chan_beatty_rcrs_demo': 'demos/chan_beatty_rcrs_demo.c',
  }
endif

uprogs_targets = []
foreach name, path : uprogs
  incs = [include_directories('.', 'include', 'proto')]
  deps = [libos]
  if use_capnp
    incs += include_directories('libos/capnp')
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

executable('phoenix_prof', 'tools/phoenix_metrics.c',
           include_directories: include_directories('.'),
           install: false,
           c_args: common_cargs + ['-DPHOENIX_METRICS_MAIN'])

subdir('tests/microbench')
subdir('tests')

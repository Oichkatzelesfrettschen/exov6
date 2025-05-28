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
  kernel = executable('kernel', ['arch/mcu/startup.c', 'src/engine/kernel/picokernel.c', 'src/engine/user/blink.c'],
      include_directories: include_directories('.', 'src/engine/include', 'arch/mcu'),
      install: false,
      c_args: common_cargs)
  subdir_done()
endif
clang_tidy = find_program('clang-tidy', required: false)
bison = find_program('bison', required: false)
if bison.found()
  example_parser = custom_target('example_parser',
    input: 'src/engine/proto/example.y',
    output: ['example_parser.c', 'example_parser.h'],
    command: [bison, '--defines=@OUTPUT1@', '-o', '@OUTPUT0@', '@INPUT@'])
endif

# User-space runtime library
mock_capnpc = find_program('scripts/mock_capnpc.sh')
capnp_targets = []
if use_capnp
  driver_capnp = custom_target('driver_capnp',
      input: 'src/engine/proto/driver.capnp',
      output: ['driver.capnp.c', 'driver.capnp.h'],
      command: [mock_capnpc, '@INPUT@'])
  hello_capnp = custom_target('hello_capnp',
      input: 'src/engine/proto/hello.capnp',
      output: ['hello.capnp.c', 'hello.capnp.h'],
      command: [mock_capnpc, '@INPUT@'])
  capnp_targets += [driver_capnp, hello_capnp]
  libcapnp = static_library('libcapnp',
      ['src/engine/libos/capnp/capnp_helpers.c'] + capnp_targets,
      include_directories: include_directories('.', 'src/engine/include', 'src/engine/proto', 'src/engine/libos/capnp'),
      c_args: common_cargs)
endif

libos_sources = [
  'src/engine/user/ulib.c',
  'src/engine/user/printf.c',
  'src/engine/user/umalloc.c',
  'src/engine/user/caplib.c',
  'src/engine/user/chan.c',
  'src/engine/user/door.c',
  'src/engine/user/math_core.c',
  'src/engine/user/libos/sched.c',
  'src/engine/libos/fs.c',
  'src/engine/libos/file.c',
  'src/engine/libos/driver.c',
  'src/engine/libos/affine_runtime.c',
  'src/engine/libos/env.c',
  'src/engine/libos/ipc.c',
  'src/engine/libos/posix.c',
  'src/engine/libos/termios.c',
  'src/engine/libos/microkernel/cap.c',
  'src/engine/libos/microkernel/msg_router.c',
  'src/engine/libos/microkernel/resource_account.c',
  'src/engine/libos/microkernel/registration.c',
]

libos = static_library('libos', libos_sources,
    include_directories: include_directories('.', 'src/engine/include', 'src/engine/proto', 'src/engine/libos/include', 'src/engine/libos/capnp'),
    c_args: common_cargs)

src_dirs = [
  'kernel/hypervisor',
  'kernel/pico',
  'src/engine/kernel',
  'src/engine/user',
  'src/engine/user/demos',
  'src/engine/libos',
  'src/userspace/libposix',
  'src/userspace/libbaremetal',
  'src/userspace/lib9p',
  'arch/generic',
  'arch/x86/legacy',
  'arch/x86/modern',
]

sources = []
foreach d : src_dirs
  sources += files(d + '/*.c')
endforeach

kernel = executable('kernel', sources,
           include_directories: include_directories('.',
                                            'src/engine/include',
                                            'src/engine/kernel/include',
                                            'kernel/hypervisor',
                                            'kernel/pico',
                                            'src/engine/proto',
                                            'src/engine/libos/include',
                                            'src/engine/libos/capnp',
                                            'src/userspace/libposix',
                                            'src/userspace/libbaremetal',
                                            'src/userspace/lib9p',
                                            'arch/generic',
                                            'arch/x86/legacy',
                                            'arch/x86/modern'),
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

subdir('src/libnstr_graph')

# User-space programs
uprogs = {
  'cat': 'src/engine/user/cat.c',
  'echo': 'src/engine/user/echo.c',
  'forktest': 'src/engine/user/forktest.c',
  'grep': 'src/engine/user/grep.c',
  'init': 'src/engine/user/init.c',
  'kill': 'src/engine/user/kill.c',
  'ln': 'src/engine/user/ln.c',
  'ls': 'src/engine/user/ls.c',
  'mkdir': 'src/engine/user/mkdir.c',
  'rm': 'src/engine/user/rm.c',
  'sh': 'src/engine/user/sh.c',
  'stressfs': 'src/engine/user/stressfs.c',
  'usertests': 'src/engine/user/usertests.c',
  'wc': 'src/engine/user/wc.c',
  'zombie': 'src/engine/user/zombie.c',
  'phi': 'src/engine/user/phi.c',
  'exo_stream_demo': 'src/engine/user/demos/exo_stream_demo.c',
  'dag_demo': 'src/engine/user/demos/dag_demo.c',
  'beatty_demo': 'src/engine/user/demos/beatty_demo.c',
  'beatty_dag_demo': 'src/engine/user/demos/beatty_dag_demo.c',
  'ipc_test': 'src/engine/user/ipc_test.c',
  'nbtest': 'src/engine/user/nbtest.c',
  'fileserver': 'src/engine/user/fileserver.c',
  'rcrs': 'src/engine/user/rcrs.c',
  'libos_posix_test': 'src/engine/user/libos_posix_test.c',
  'libos_posix_extra_test': 'src/engine/user/demos/libos_posix_extra_test.c',
  'qspin_demo': 'src/engine/user/demos/qspin_demo.c',
  'tty_demo': 'src/engine/user/tty_demo.c',
  'termios_demo': 'src/engine/user/termios_demo.c',
  'msgqueue_demo': 'src/engine/user/demos/msgqueue_demo.c',
  'fib_big_demo': 'src/engine/user/demos/fib_big_demo.c',
  'start_guest': 'src/engine/user/start_guest.c',
  'hv_demo': 'src/engine/user/demos/hv_demo.c',
}

if use_capnp
  uprogs += {
    'pingdriver': 'src/engine/user/pingdriver.c',
    'typed_chan_demo': 'src/engine/user/demos/typed_chan_demo.c',
    'typed_chan_send': 'src/engine/user/demos/typed_chan_send.c',
    'typed_chan_recv': 'src/engine/user/demos/typed_chan_recv.c',
    'affine_channel_demo': 'src/engine/user/demos/affine_channel_demo.c',
    'chan_dag_supervisor_demo': 'src/engine/user/demos/chan_dag_supervisor_demo.c',
    'chan_beatty_rcrs_demo': 'src/engine/user/demos/chan_beatty_rcrs_demo.c',
  }
endif

uprogs_targets = []
foreach name, path : uprogs
  incs = [include_directories('.', 'src/engine/include', 'src/engine/proto', 'src/engine/libos/include')]
  deps = [libos]
  if use_capnp
    incs += include_directories('src/engine/libos/capnp')
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

executable('phoenix_prof', 'tools/profiling/phoenix_metrics.c',
           include_directories: include_directories('.'),
           install: false,
           c_args: common_cargs + ['-DPHOENIX_METRICS_MAIN'])

subdir('tests/microbench')
subdir('tests/posix')

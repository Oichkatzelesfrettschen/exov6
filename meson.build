project('xv6', 'c', default_options: ['c_std=c23'])
add_project_arguments('-Wall', '-Werror', language: ['c', 'cpp'])

use_ticket_lock = get_option('use_ticket_lock')
ipc_debug = get_option('ipc_debug')
use_capnp = get_option('use_capnp')
mcu = get_option('mcu') # Define mcu as a Meson option
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
  'libos/sched.c', # Corrected path
  'libos/fs.c',
  'libos/file.c',
  # 'libos/driver.c', // Removed, file not found
  'libos/affine_runtime.c',
  # 'libos/env.c', // Removed, file not found
  'libos/ipc.c',
  'libos/posix.c',
  'libos/termios.c',
  'libos/cap.c', # Corrected path
  'libos/msg_router.c', # Corrected path
  'libos/resource_account.c', # Corrected path
  'libos/registration.c', # Corrected path
]

libos = static_library('libos', libos_sources,
    include_directories: include_directories('.', 'include', 'proto', 'libos/capnp'),
    c_args: common_cargs)

src_dirs = [
  # 'kernel/hypervisor', # Removed as it contains no .c files, only .h
  # 'kernel', # Problematic: assuming .c files are in subdirs, not directly here
  # 'user',   # Problematic: assuming .c files are in subdirs, not directly here
  'demos',
  'libos', # Assuming this dir and subdirs listed below have .c files directly or are handled
  'libos/stubs',
  'src/arch/generic',
  'src/arch/x86/legacy',
  'src/arch/x86/modern',
]

sources = []
foreach d : src_dirs
  # This pattern is failing for top-level 'kernel' and 'user'
  # It might work for the remaining more specific dirs if they contain .c files directly
  sources += files(meson.current_source_dir() / d / '*.c')
endforeach

# Removing the explicit list of kernel files for now to isolate the globbing issue.
# If Meson configures with an empty/partial 'sources' for the kernel,
# it means the globbing for 'kernel' and 'user' is the primary problem.

kernel = executable('kernel', sources, # This will likely be an empty sources list for now
           include_directories: include_directories('.',
                                            'include',
                                            'kernel/include', # May or may not exist, but good to keep if it does
                                           'kernel/hypervisor',
                                            'proto',
                                            'libos/capnp', # if use_capnp
                                            'libos/stubs',
                                            'src', # Broad include
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
  'test_qspin': 'kernel/test_quaternion_spinlock.c',
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

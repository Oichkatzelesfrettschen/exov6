project('xv6', 'c',
  default_options : ['c_std=c17']
)

add_project_arguments('-Wall', '-Werror', language : ['c', 'cpp'])

# User-configurable options
option('use_ticket_lock',
  type : 'boolean',
  value : false,
  description : 'Enable ticket-based spinlock implementation'
)
option('ipc_debug',
  type : 'boolean',
  value : false,
  description : 'Enable extra IPC debug instrumentation'
)
option('use_capnp',
  type : 'boolean',
  value : false,
  description : 'Enable Cap’n Proto support for IPC definitions'
)
option('mcu',
  type : 'boolean',
  value : false,
  description : 'Build the MCU-specific kernel variant'
)

# Collect common C compiler arguments based on options
common_cargs = []
if get_option('use_ticket_lock')
  common_cargs += ['-DUSE_TICKET_LOCK']
endif
if get_option('ipc_debug')
  common_cargs += ['-DIPC_DEBUG']
endif

# Detect decimal float support
cc = meson.get_compiler('c')
if cc.has_argument('-mdecimal-float')
  common_cargs += ['-mdecimal-float', '-DHAVE_DECIMAL_FLOAT']
endif

# MCU-specific kernel target
if get_option('mcu')
  mcu_kernel = executable(
    'kernel-mcu',
    ['src/arch/mcu/startup.c', 'kernel/picokernel.c', 'user/blink.c'],
    include_directories: include_directories(
      '.', 'include', 'src', 'src/arch/mcu'
    ),
    install: false,
    c_args: common_cargs
  )
endif

# Optional Bison parser generation
bison = find_program('bison', required: false)
if bison.found()
  example_parser = custom_target(
    'example_parser',
    input : 'proto/example.y',
    output : ['example_parser.c', 'example_parser.h'],
    command : [bison, '--defines=@OUTPUT1@', '-o', '@OUTPUT0@', '@INPUT@']
  )
endif

# Cap’n Proto code generation
if get_option('use_capnp')
  mock_capnpc = find_program('scripts/mock_capnpc.sh', required: true)
  driver_capnp = custom_target(
    'driver_capnp',
    input  : 'proto/driver.capnp',
    output : ['driver.capnp.c', 'driver.capnp.h'],
    command: [mock_capnpc, '@INPUT@']
  )
  hello_capnp = custom_target(
    'hello_capnp',
    input  : 'proto/hello.capnp',
    output : ['hello.capnp.c', 'hello.capnp.h'],
    command: [mock_capnpc, '@INPUT@']
  )
  capnp_targets = [ driver_capnp, hello_capnp ]
  libcapnp = static_library(
    'capnp',
    ['libos/capnp/capnp_helpers.c'] + capnp_targets,
    include_directories: include_directories(
      '.', 'include', 'proto', 'libos/capnp'
    ),
    c_args: common_cargs
  )
endif

# libos static library
libos_sources = [
  'user/ulib.c', 'user/printf.c', 'user/umalloc.c', 'user/caplib.c',
  'user/chan.c', 'user/door.c', 'user/math_core.c',
  'libos/sched.c', 'libos/fs.c', 'libos/file.c',
  'libos/affine_runtime.c', 'libos/ipc.c',
  'libos/posix.c', 'libos/termios.c',
  'libos/cap.c', 'libos/msg_router.c',
  'libos/resource_account.c', 'libos/registration.c'
]

libos = static_library(
  'os',
  libos_sources,
  include_directories: include_directories(
    '.', 'include', 'proto', 'libos/capnp'
  ),
  c_args: common_cargs
)

# Gather kernel and library source directories
src_dirs = [
  'demos', 'libos', 'libos/stubs',
  'src/arch/generic', 'src/arch/x86/legacy', 'src/arch/x86/modern'
]

all_sources = []
foreach d : src_dirs
  all_sources += files(d + '/*.c')
endforeach

# Kernel executable
kernel = executable(
  'kernel',
  all_sources,
  include_directories: include_directories(
    '.', 'include', 'kernel/include', 'kernel/hypervisor',
    'proto', 'libos/capnp', 'libos/stubs',
    'src', 'src/arch/x86/legacy', 'src/arch/x86/modern'
  ),
  install: false,
  c_args: common_cargs,
  link_with: [ libos ] + (get_option('use_capnp') ? [ libcapnp ] : [])
)

# QEMU launcher
qemu = find_program(['qemu-system-x86_64', 'qemu-system-i386', 'qemu'], required: false)
if qemu.found()
  run_target(
    'qemu-nox',
    command : [ qemu, '-nographic', '-serial', 'stdio', '-kernel', kernel.full_path() ],
    depends : kernel,
    console : true
  )
endif
project('xv6', 'c',
  default_options : ['c_std=c2x']
)

add_project_arguments('-Wall', '-Werror', language : ['c', 'cpp'])

# User-configurable options are declared in meson_options.txt

# Collect common C compiler arguments based on options
common_cargs = []
common_link_args = []

if get_option('use_ticket_lock')
  common_cargs += ['-DUSE_TICKET_LOCK']
endif
if get_option('ipc_debug')
  common_cargs += ['-DIPC_DEBUG']
endif

# Modern LLVM toolchain configuration
cc = meson.get_compiler('c')

# Configure LLD linker
if get_option('use_lld')
  if cc.get_id() == 'clang'
    common_link_args += ['-fuse-ld=lld']
    message('Using LLVM LLD linker')
  else
    warning('LLD linker requires Clang compiler')
  endif
endif

# Configure Link Time Optimization (ThinLTO)
if get_option('use_lto')
  if cc.get_id() == 'clang'
    common_cargs += ['-flto=thin']
    common_link_args += ['-flto=thin']
    message('Enabled LLVM ThinLTO')
  else
    warning('LTO requires Clang compiler for LLVM ThinLTO')
  endif
endif

# Configure Polly optimizations
if get_option('use_polly')
  if cc.get_id() == 'clang'
    polly_args = [
      '-mllvm', '-polly',
      '-mllvm', '-polly-vectorizer=stripmine',
      '-mllvm', '-polly-parallel'
    ]
    if cc.has_multi_arguments(polly_args)
      common_cargs += polly_args
      message('Enabled LLVM Polly optimizations')
    else
      warning('Polly optimizations not supported by this Clang version')
    endif
  else
    warning('Polly optimizations require Clang compiler')
  endif
endif

# Configure sanitizers
if get_option('enable_asan')
  asan_args = ['-fsanitize=address', '-fno-omit-frame-pointer']
  if cc.has_multi_arguments(asan_args)
    common_cargs += asan_args
    common_link_args += ['-fsanitize=address']
    message('Enabled AddressSanitizer')
  else
    warning('AddressSanitizer not supported by this compiler')
  endif
endif

if get_option('enable_tsan')
  tsan_args = ['-fsanitize=thread']
  if cc.has_multi_arguments(tsan_args)
    common_cargs += tsan_args
    common_link_args += ['-fsanitize=thread']
    message('Enabled ThreadSanitizer')
  else
    warning('ThreadSanitizer not supported by this compiler')
  endif
endif

if get_option('enable_ubsan')
  ubsan_args = ['-fsanitize=undefined']
  if cc.has_multi_arguments(ubsan_args)
    common_cargs += ubsan_args
    common_link_args += ['-fsanitize=undefined']
    message('Enabled UndefinedBehaviorSanitizer')
  else
    warning('UndefinedBehaviorSanitizer not supported by this compiler')
  endif
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
  # Use run_command with find to get source files
  find_result = run_command('find', d, '-name', '*.c', '-type', 'f', check: false)
  if find_result.returncode() == 0
    source_files = find_result.stdout().strip().split('\n')
    foreach f : source_files
      if f != ''
        all_sources += files(f)
      endif
    endforeach
  endif
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
  link_args: common_link_args,
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

ddekit = static_library('ddekit', 'stub.c',
    include_directories: include_directories('.'),
    pic: false)

libddekit = declare_dependency(
    link_with: ddekit,
    include_directories: include_directories('.'))

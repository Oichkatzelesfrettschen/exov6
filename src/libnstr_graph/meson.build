libnstr_graph = static_library(
    'nstr_graph',
    'nstr_graph.c',
    include_directories: include_directories('.'),
    pic: false,
)

libnstr_graph_shared = shared_library(
    'nstr_graph_shared',
    'nstr_graph.c',
    include_directories: include_directories('.'),
    install: true,
    version: '0.1.0'
)

install_headers('nstr_graph.h')


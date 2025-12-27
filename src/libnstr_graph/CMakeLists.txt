# src/libnstr_graph/CMakeLists.txt - NStr Graph Library

# Create NStr Graph library using FeuerBird Exokernel framework
feuerbird_add_library(feuerbird-nstr-graph
    STATIC
    SOURCES nstr_graph.c
    INCLUDES 
        ${CMAKE_CURRENT_SOURCE_DIR}
        ${CMAKE_SOURCE_DIR}/include
)

# Create shared library variant
feuerbird_add_library(feuerbird-nstr-graph-shared
    SHARED
    SOURCES nstr_graph.c
    INCLUDES 
        ${CMAKE_CURRENT_SOURCE_DIR}
        ${CMAKE_SOURCE_DIR}/include
)

# Set output name for shared library
set_target_properties(feuerbird-nstr-graph-shared PROPERTIES 
    OUTPUT_NAME "feuerbird-nstr-graph"
    PREFIX "lib"
)

# Legacy aliases for backward compatibility
add_library(nstr_graph ALIAS feuerbird-nstr-graph)
add_library(nstr_graph_shared ALIAS feuerbird-nstr-graph-shared)

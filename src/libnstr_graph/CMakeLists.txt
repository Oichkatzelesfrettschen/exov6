# src/libnstr_graph/CMakeLists.txt - NStr Graph Library

# Create NStr Graph library using ExoV6 framework
exov6_add_library(exov6-nstr-graph
    STATIC
    SOURCES nstr_graph.c
    INCLUDES 
        ${CMAKE_CURRENT_SOURCE_DIR}
        ${CMAKE_SOURCE_DIR}/include
)

# Create shared library variant
exov6_add_library(exov6-nstr-graph-shared
    SHARED
    SOURCES nstr_graph.c
    INCLUDES 
        ${CMAKE_CURRENT_SOURCE_DIR}
        ${CMAKE_SOURCE_DIR}/include
)

# Set output name for shared library
set_target_properties(exov6-nstr-graph-shared PROPERTIES 
    OUTPUT_NAME "exov6-nstr-graph"
    PREFIX "lib"
)

# Legacy aliases for backward compatibility
add_library(nstr_graph ALIAS exov6-nstr-graph)
add_library(nstr_graph_shared ALIAS exov6-nstr-graph-shared)

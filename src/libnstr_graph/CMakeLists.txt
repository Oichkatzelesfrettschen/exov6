# src/libnstr_graph/CMakeLists.txt - NStr Graph Library

# Create NStr Graph library using ExoV6 framework
phoenix_add_library(phoenix-nstr-graph
    STATIC
    SOURCES nstr_graph.c
    INCLUDES 
        ${CMAKE_CURRENT_SOURCE_DIR}
        ${CMAKE_SOURCE_DIR}/include
)

# Create shared library variant (Disabled: platform doesn't support shared libs)
# phoenix_add_library(phoenix-nstr-graph-shared
#     SHARED
#     SOURCES nstr_graph.c
#     INCLUDES
#         ${CMAKE_CURRENT_SOURCE_DIR}
#         ${CMAKE_SOURCE_DIR}/include
# )

# Set output name for shared library
# set_target_properties(phoenix-nstr-graph-shared PROPERTIES
#     OUTPUT_NAME "phoenix-nstr-graph"
#     PREFIX "lib"
# )

# Legacy aliases for backward compatibility
add_library(nstr_graph ALIAS phoenix-nstr-graph)
# add_library(nstr_graph_shared ALIAS phoenix-nstr-graph-shared)

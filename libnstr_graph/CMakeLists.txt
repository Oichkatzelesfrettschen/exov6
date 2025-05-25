add_library(nstr_graph STATIC nstr_graph.c)

# Provide the include directory to consumers
target_include_directories(nstr_graph PUBLIC ${CMAKE_CURRENT_SOURCE_DIR})

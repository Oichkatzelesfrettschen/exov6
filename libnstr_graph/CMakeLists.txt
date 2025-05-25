add_library(nstr_graph STATIC nstr_graph.c)

set_target_properties(nstr_graph PROPERTIES POSITION_INDEPENDENT_CODE OFF)

target_include_directories(nstr_graph PUBLIC ${CMAKE_CURRENT_SOURCE_DIR})

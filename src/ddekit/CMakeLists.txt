add_library(ddekit STATIC stub.c)
set_target_properties(ddekit PROPERTIES POSITION_INDEPENDENT_CODE OFF)
target_include_directories(ddekit PUBLIC ${CMAKE_CURRENT_SOURCE_DIR})

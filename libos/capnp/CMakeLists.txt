add_library(capnp STATIC capnp_helpers.c)
set_target_properties(capnp PROPERTIES POSITION_INDEPENDENT_CODE OFF)
target_include_directories(capnp PUBLIC ${CMAKE_CURRENT_SOURCE_DIR})

add_library(capnp_shared SHARED capnp_helpers.c)
set_target_properties(capnp_shared PROPERTIES OUTPUT_NAME capnp)
target_include_directories(capnp_shared PUBLIC ${CMAKE_CURRENT_SOURCE_DIR})

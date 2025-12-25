# IPC Demonstration Programs
# Showcases advanced IPC and mathematical optimization capabilities

# Advanced IPC showcase
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/advanced_ipc_showcase.c")
    phoenix_add_executable(advanced-ipc-showcase
        SOURCES advanced_ipc_showcase.c
        INCLUDES 
            ${CMAKE_CURRENT_SOURCE_DIR}
            ${CMAKE_SOURCE_DIR}/include
        DEPENDENCIES phoenix-libos
    )
    
    target_link_libraries(advanced-ipc-showcase PRIVATE m)
    
    set_target_properties(advanced-ipc-showcase PROPERTIES 
        OUTPUT_NAME "advanced-ipc-showcase"
        PREFIX ""
    )
endif()

# IPC showcase demo
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/demo_ipc_showcase.c")
    phoenix_add_executable(demo-ipc-showcase
        SOURCES demo_ipc_showcase.c
        INCLUDES 
            ${CMAKE_CURRENT_SOURCE_DIR}
            ${CMAKE_SOURCE_DIR}/include
        DEPENDENCIES phoenix-libos
    )
    
    target_link_libraries(demo-ipc-showcase PRIVATE m)
    
    set_target_properties(demo-ipc-showcase PROPERTIES 
        OUTPUT_NAME "demo-ipc-showcase"
        PREFIX ""
    )
endif()

message(STATUS "IPC demos configured:")
message(STATUS "  - Advanced IPC showcase: ✓")
message(STATUS "  - IPC demo showcase: ✓")
# demos/CMakeLists.txt - Demonstration Programs

# ═════════════════════════════════════════════════════════════════════
# CORE DEMONSTRATION PROGRAMS
# ═════════════════════════════════════════════════════════════════════

# Message queue demonstration
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/msgqueue_demo.c")
    phoenix_add_executable(msgqueue-demo
        SOURCES msgqueue_demo.c
        INCLUDES 
            ${CMAKE_CURRENT_SOURCE_DIR}
            ${CMAKE_SOURCE_DIR}/include
            ${CMAKE_SOURCE_DIR}/proto
        DEPENDENCIES 
            phoenix-libos 
            phoenix-nstr-graph
    )
    
    # Add Cap'n Proto if enabled
    if(USE_CAPNP AND TARGET phoenix-capnp)
        target_link_libraries(msgqueue-demo PRIVATE phoenix-capnp)
    endif()
    
    set_target_properties(msgqueue-demo PROPERTIES 
        OUTPUT_NAME "msgqueue-demo"
        PREFIX ""
    )
endif()

# Fibonacci big number demonstration
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/fib_big_demo.c")
    phoenix_add_executable(fib-big-demo
        SOURCES fib_big_demo.c
        INCLUDES 
            ${CMAKE_CURRENT_SOURCE_DIR}
            ${CMAKE_SOURCE_DIR}/include
            ${CMAKE_SOURCE_DIR}/proto
        DEPENDENCIES 
            phoenix-libos 
            phoenix-nstr-graph
    )
    
    if(USE_CAPNP AND TARGET phoenix-capnp)
        target_link_libraries(fib-big-demo PRIVATE phoenix-capnp)
    endif()
    
    set_target_properties(fib-big-demo PROPERTIES 
        OUTPUT_NAME "fib-big-demo"
        PREFIX ""
    )
endif()

# Wumpus game
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/wumpus.c")
    phoenix_add_executable(wumpus-game
        SOURCES wumpus.c
        INCLUDES 
            ${CMAKE_CURRENT_SOURCE_DIR}
            ${CMAKE_SOURCE_DIR}/include
        DEPENDENCIES phoenix-libos
    )
    
    set_target_properties(wumpus-game PROPERTIES 
        OUTPUT_NAME "wumpus"
        PREFIX ""
    )
endif()

# ═════════════════════════════════════════════════════════════════════
# CHANNEL AND IPC DEMONSTRATIONS
# ═════════════════════════════════════════════════════════════════════

# Hello channel demo
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/hello_channel.c")
    phoenix_add_executable(hello-channel-demo
        SOURCES hello_channel.c
        INCLUDES 
            ${CMAKE_CURRENT_SOURCE_DIR}
            ${CMAKE_SOURCE_DIR}/include
        DEPENDENCIES phoenix-libos
    )
    
    set_target_properties(hello-channel-demo PROPERTIES 
        OUTPUT_NAME "hello-channel"
        PREFIX ""
    )
endif()

# Typed channel demo
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/typed_chan_demo.c")
    phoenix_add_executable(typed-chan-demo
        SOURCES typed_chan_demo.c
        INCLUDES 
            ${CMAKE_CURRENT_SOURCE_DIR}
            ${CMAKE_SOURCE_DIR}/include
        DEPENDENCIES phoenix-libos
    )
    
    set_target_properties(typed-chan-demo PROPERTIES 
        OUTPUT_NAME "typed-chan-demo"
        PREFIX ""
    )
endif()

# Typed channel send/receive demos
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/typed_chan_send.c")
    phoenix_add_executable(typed-chan-send
        SOURCES typed_chan_send.c
        INCLUDES 
            ${CMAKE_CURRENT_SOURCE_DIR}
            ${CMAKE_SOURCE_DIR}/include
        DEPENDENCIES phoenix-libos
    )
    
    set_target_properties(typed-chan-send PROPERTIES 
        OUTPUT_NAME "typed-chan-send"
        PREFIX ""
    )
endif()

if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/typed_chan_recv.c")
    phoenix_add_executable(typed-chan-recv
        SOURCES typed_chan_recv.c
        INCLUDES 
            ${CMAKE_CURRENT_SOURCE_DIR}
            ${CMAKE_SOURCE_DIR}/include
        DEPENDENCIES phoenix-libos
    )
    
    set_target_properties(typed-chan-recv PROPERTIES 
        OUTPUT_NAME "typed-chan-recv"
        PREFIX ""
    )
endif()

# Affine channel demo
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/affine_channel_demo.c")
    phoenix_add_executable(affine-channel-demo
        SOURCES affine_channel_demo.c
        INCLUDES 
            ${CMAKE_CURRENT_SOURCE_DIR}
            ${CMAKE_SOURCE_DIR}/include
        DEPENDENCIES phoenix-libos
    )
    
    set_target_properties(affine-channel-demo PROPERTIES 
        OUTPUT_NAME "affine-channel-demo"
        PREFIX ""
    )
endif()

# ═════════════════════════════════════════════════════════════════════
# SCHEDULING AND DAG DEMONSTRATIONS
# ═════════════════════════════════════════════════════════════════════

# Beatty scheduler demo
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/beatty_demo.c")
    phoenix_add_executable(beatty-demo
        SOURCES beatty_demo.c
        INCLUDES 
            ${CMAKE_CURRENT_SOURCE_DIR}
            ${CMAKE_SOURCE_DIR}/include
        DEPENDENCIES phoenix-libos
    )
    
    set_target_properties(beatty-demo PROPERTIES 
        OUTPUT_NAME "beatty-demo"
        PREFIX ""
    )
endif()

# DAG demo
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/dag_demo.c")
    phoenix_add_executable(dag-demo
        SOURCES dag_demo.c
        INCLUDES 
            ${CMAKE_CURRENT_SOURCE_DIR}
            ${CMAKE_SOURCE_DIR}/include
        DEPENDENCIES phoenix-libos
    )
    
    set_target_properties(dag-demo PROPERTIES 
        OUTPUT_NAME "dag-demo"
        PREFIX ""
    )
endif()

# Beatty DAG demo
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/beatty_dag_demo.c")
    phoenix_add_executable(beatty-dag-demo
        SOURCES beatty_dag_demo.c
        INCLUDES 
            ${CMAKE_CURRENT_SOURCE_DIR}
            ${CMAKE_SOURCE_DIR}/include
        DEPENDENCIES phoenix-libos
    )
    
    set_target_properties(beatty-dag-demo PROPERTIES 
        OUTPUT_NAME "beatty-dag-demo"
        PREFIX ""
    )
endif()

# Channel Beatty RCRS demo
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/chan_beatty_rcrs_demo.c")
    phoenix_add_executable(chan-beatty-rcrs-demo
        SOURCES chan_beatty_rcrs_demo.c
        INCLUDES 
            ${CMAKE_CURRENT_SOURCE_DIR}
            ${CMAKE_SOURCE_DIR}/include
        DEPENDENCIES phoenix-libos
    )
    
    set_target_properties(chan-beatty-rcrs-demo PROPERTIES 
        OUTPUT_NAME "chan-beatty-rcrs-demo"
        PREFIX ""
    )
endif()

# Channel DAG supervisor demo
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/chan_dag_supervisor_demo.c")
    phoenix_add_executable(chan-dag-supervisor-demo
        SOURCES chan_dag_supervisor_demo.c
        INCLUDES 
            ${CMAKE_CURRENT_SOURCE_DIR}
            ${CMAKE_SOURCE_DIR}/include
        DEPENDENCIES phoenix-libos
    )
    
    set_target_properties(chan-dag-supervisor-demo PROPERTIES 
        OUTPUT_NAME "chan-dag-supervisor-demo"
        PREFIX ""
    )
endif()

# ═════════════════════════════════════════════════════════════════════
# HARDWARE AND SYSTEM DEMONSTRATIONS
# ═════════════════════════════════════════════════════════════════════

# Frame buffer device demo
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/fbdev_demo.c")
    phoenix_add_executable(fbdev-demo
        SOURCES fbdev_demo.c
        INCLUDES 
            ${CMAKE_CURRENT_SOURCE_DIR}
            ${CMAKE_SOURCE_DIR}/include
        DEPENDENCIES phoenix-libos
    )
    
    set_target_properties(fbdev-demo PROPERTIES 
        OUTPUT_NAME "fbdev-demo"
        PREFIX ""
    )
endif()

# Hypervisor demo
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/hv_demo.c")
    phoenix_add_executable(hv-demo
        SOURCES hv_demo.c
        INCLUDES 
            ${CMAKE_CURRENT_SOURCE_DIR}
            ${CMAKE_SOURCE_DIR}/include
        DEPENDENCIES phoenix-libos
    )
    
    set_target_properties(hv-demo PROPERTIES 
        OUTPUT_NAME "hv-demo"
        PREFIX ""
    )
endif()

# DDEKit port demo
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/ddekit_port_demo.c")
    phoenix_add_executable(ddekit-port-demo
        SOURCES ddekit_port_demo.c
        INCLUDES 
            ${CMAKE_CURRENT_SOURCE_DIR}
            ${CMAKE_SOURCE_DIR}/include
        DEPENDENCIES phoenix-libos phoenix-libos-ddekit
    )
    
    set_target_properties(ddekit-port-demo PROPERTIES 
        OUTPUT_NAME "ddekit-port-demo"
        PREFIX ""
    )
endif()

# ═════════════════════════════════════════════════════════════════════
# SYNCHRONIZATION DEMONSTRATIONS
# ═════════════════════════════════════════════════════════════════════

# Queue spinlock demo
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/qspin_demo.c")
    phoenix_add_executable(qspin-demo
        SOURCES qspin_demo.c
        INCLUDES 
            ${CMAKE_CURRENT_SOURCE_DIR}
            ${CMAKE_SOURCE_DIR}/include
        DEPENDENCIES phoenix-libos
    )
    
    set_target_properties(qspin-demo PROPERTIES 
        OUTPUT_NAME "qspin-demo"
        PREFIX ""
    )
endif()

# ═════════════════════════════════════════════════════════════════════
# MICROKERNEL AND POLICY DEMONSTRATIONS
# ═════════════════════════════════════════════════════════════════════

# Microkernel RCRS demo
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/microkernel_rcrs_demo.c")
    phoenix_add_executable(microkernel-rcrs-demo
        SOURCES microkernel_rcrs_demo.c
        INCLUDES 
            ${CMAKE_CURRENT_SOURCE_DIR}
            ${CMAKE_SOURCE_DIR}/include
        DEPENDENCIES phoenix-libos
    )
    
    set_target_properties(microkernel-rcrs-demo PROPERTIES 
        OUTPUT_NAME "microkernel-rcrs-demo"
        PREFIX ""
    )
endif()

# IRQ lambda policy demo
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/irq_lambda_policy.c")
    phoenix_add_executable(irq-lambda-policy-demo
        SOURCES irq_lambda_policy.c
        INCLUDES 
            ${CMAKE_CURRENT_SOURCE_DIR}
            ${CMAKE_SOURCE_DIR}/include
        DEPENDENCIES phoenix-libos
    )
    
    set_target_properties(irq-lambda-policy-demo PROPERTIES 
        OUTPUT_NAME "irq-lambda-policy-demo"
        PREFIX ""
    )
endif()

# ═════════════════════════════════════════════════════════════════════
# POSIX COMPATIBILITY DEMONSTRATIONS
# ═════════════════════════════════════════════════════════════════════

# POSIX LibOS extra test
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/libos_posix_extra_test.c")
    phoenix_add_executable(libos-posix-extra-test
        SOURCES libos_posix_extra_test.c
        INCLUDES 
            ${CMAKE_CURRENT_SOURCE_DIR}
            ${CMAKE_SOURCE_DIR}/include
        DEPENDENCIES phoenix-libos
    )
    
    set_target_properties(libos-posix-extra-test PROPERTIES 
        OUTPUT_NAME "libos-posix-extra-test"
        PREFIX ""
    )
endif()

# POSIX current working directory test
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/posix_cwd_test.c")
    phoenix_add_executable(posix-cwd-test
        SOURCES posix_cwd_test.c
        INCLUDES 
            ${CMAKE_CURRENT_SOURCE_DIR}
            ${CMAKE_SOURCE_DIR}/include
        DEPENDENCIES phoenix-libos
    )
    
    set_target_properties(posix-cwd-test PROPERTIES 
        OUTPUT_NAME "posix-cwd-test"
        PREFIX ""
    )
endif()

# POSIX miscellaneous test
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/posix_misc_test.c")
    phoenix_add_executable(posix-misc-test
        SOURCES posix_misc_test.c
        INCLUDES 
            ${CMAKE_CURRENT_SOURCE_DIR}
            ${CMAKE_SOURCE_DIR}/include
        DEPENDENCIES phoenix-libos
    )
    
    set_target_properties(posix-misc-test PROPERTIES 
        OUTPUT_NAME "posix-misc-test"
        PREFIX ""
    )
endif()

# POSIX socket test
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/posix_socket_test.c")
    phoenix_add_executable(posix-socket-test
        SOURCES posix_socket_test.c
        INCLUDES 
            ${CMAKE_CURRENT_SOURCE_DIR}
            ${CMAKE_SOURCE_DIR}/include
        DEPENDENCIES phoenix-libos
    )
    
    set_target_properties(posix-socket-test PROPERTIES 
        OUTPUT_NAME "posix-socket-test"
        PREFIX ""
    )
endif()

# ═════════════════════════════════════════════════════════════════════
# STREAMING DEMONSTRATIONS
# ═════════════════════════════════════════════════════════════════════

# ExoStream demo
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/exo_stream_demo.c")
    phoenix_add_executable(exo-stream-demo
        SOURCES exo_stream_demo.c
        INCLUDES 
            ${CMAKE_CURRENT_SOURCE_DIR}
            ${CMAKE_SOURCE_DIR}/include
        DEPENDENCIES phoenix-libos
    )
    
    set_target_properties(exo-stream-demo PROPERTIES 
        OUTPUT_NAME "exo-stream-demo"
        PREFIX ""
    )
endif()

# ═════════════════════════════════════════════════════════════════════
# PYTHON DEMONSTRATIONS
# ═════════════════════════════════════════════════════════════════════

# Flow control tuning demo (Python)
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/fc_tuning_demo.py")
    find_package(Python3 COMPONENTS Interpreter)
    
    if(Python3_FOUND)
        configure_file(
            "${CMAKE_CURRENT_SOURCE_DIR}/fc_tuning_demo.py"
            "${CMAKE_BINARY_DIR}/bin/fc-tuning-demo"
            COPYONLY
        )
        
        if(UNIX)
            file(CHMOD "${CMAKE_BINARY_DIR}/bin/fc-tuning-demo" 
                PERMISSIONS OWNER_READ OWNER_WRITE OWNER_EXECUTE 
                           GROUP_READ GROUP_EXECUTE 
                           WORLD_READ WORLD_EXECUTE
            )
        endif()
    endif()
endif()

# Test POSIX extra (Python)
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/test_posix_extra.py")
    find_package(Python3 COMPONENTS Interpreter)
    
    if(Python3_FOUND)
        configure_file(
            "${CMAKE_CURRENT_SOURCE_DIR}/test_posix_extra.py"
            "${CMAKE_BINARY_DIR}/bin/test-posix-extra"
            COPYONLY
        )
        
        if(UNIX)
            file(CHMOD "${CMAKE_BINARY_DIR}/bin/test-posix-extra" 
                PERMISSIONS OWNER_READ OWNER_WRITE OWNER_EXECUTE 
                           GROUP_READ GROUP_EXECUTE 
                           WORLD_READ WORLD_EXECUTE
            )
        endif()
    endif()
endif()

# ═════════════════════════════════════════════════════════════════════
# CUSTOM TARGETS FOR RUNNING DEMOS
# ═════════════════════════════════════════════════════════════════════

# Demo runner targets
if(TARGET phoenix-msgqueue-demo)
    add_custom_target(run-msgqueue-demo
        COMMAND phoenix-msgqueue-demo
        DEPENDS phoenix-msgqueue-demo
        COMMENT "Running message queue demonstration"
    )
endif()

if(TARGET phoenix-wumpus-game)
    add_custom_target(run-wumpus
        COMMAND phoenix-wumpus-game
        DEPENDS phoenix-wumpus-game
        COMMENT "Running Wumpus game"
    )
endif()

# ═════════════════════════════════════════════════════════════════════
# EXPORTS
# ═════════════════════════════════════════════════════════════════════

# Collect all demo targets
set(DEMO_TARGETS)
get_directory_property(ALL_TARGETS BUILDSYSTEM_TARGETS)
foreach(target ${ALL_TARGETS})
    if(target MATCHES "^phoenix-.*-demo$" OR target MATCHES "^phoenix-.*-test$" OR target STREQUAL "phoenix-wumpus-game")
        list(APPEND DEMO_TARGETS ${target})
    endif()
endforeach()

set(EXOV6_DEMO_TARGETS ${DEMO_TARGETS} PARENT_SCOPE)

message(STATUS "Demos zone configured:")
message(STATUS "  - Core demos: ✓")
message(STATUS "  - Channel demos: ✓")
message(STATUS "  - Scheduling demos: ✓")
message(STATUS "  - POSIX demos: ✓")
message(STATUS "  - Hardware demos: ✓")
if(Python3_FOUND)
    message(STATUS "  - Python demos: ✓")
endif()
message(STATUS "  - Total demos: ${DEMO_TARGETS}")
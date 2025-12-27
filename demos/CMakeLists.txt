# demos/CMakeLists.txt - Demonstration Programs

# ═════════════════════════════════════════════════════════════════════
# CORE DEMONSTRATION PROGRAMS
# ═════════════════════════════════════════════════════════════════════

# Message queue demonstration
# NOTE: Disabled for host builds - requires kernel syscalls (exo_alloc_page)
# that are only available when running on the FeuerBird kernel
# if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/msgqueue_demo.c")
#     feuerbird_add_executable(msgqueue-demo
#         SOURCES msgqueue_demo.c
#         INCLUDES
#             ${CMAKE_CURRENT_SOURCE_DIR}
#             ${CMAKE_SOURCE_DIR}/include
#             ${CMAKE_SOURCE_DIR}/proto
#         DEPENDENCIES
#             feuerbird-libos
#             feuerbird-nstr-graph
#     )
#
#     # Add Cap'n Proto if enabled
#     if(USE_CAPNP AND TARGET feuerbird-capnp)
#         target_link_libraries(msgqueue-demo PRIVATE feuerbird-capnp)
#     endif()
#
#     set_target_properties(msgqueue-demo PROPERTIES
#         OUTPUT_NAME "msgqueue-demo"
#         PREFIX ""
#     )
# endif()

# Fibonacci big number demonstration
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/fib_big_demo.c")
    feuerbird_add_executable(fib-big-demo
        SOURCES fib_big_demo.c
        INCLUDES 
            ${CMAKE_CURRENT_SOURCE_DIR}
            ${CMAKE_SOURCE_DIR}/include
            ${CMAKE_SOURCE_DIR}/proto
        DEPENDENCIES 
            feuerbird-libos 
            feuerbird-nstr-graph
    )
    
    if(USE_CAPNP AND TARGET feuerbird-capnp)
        target_link_libraries(fib-big-demo PRIVATE feuerbird-capnp)
    endif()
    
    set_target_properties(fib-big-demo PROPERTIES 
        OUTPUT_NAME "fib-big-demo"
        PREFIX ""
    )
endif()

# Wumpus game
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/wumpus.c")
    feuerbird_add_executable(wumpus-game
        SOURCES wumpus.c
        INCLUDES 
            ${CMAKE_CURRENT_SOURCE_DIR}
            ${CMAKE_SOURCE_DIR}/include
        DEPENDENCIES feuerbird-libos
    )
    
    set_target_properties(wumpus-game PROPERTIES 
        OUTPUT_NAME "wumpus"
        PREFIX ""
    )
endif()

# ═════════════════════════════════════════════════════════════════════
# CHANNEL AND IPC DEMONSTRATIONS
# ═════════════════════════════════════════════════════════════════════

# Hello channel demo (requires Cap'n Proto for hello.capnp.h)
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/hello_channel.c" AND USE_CAPNP)
    feuerbird_add_executable(hello-channel-demo
        SOURCES hello_channel.c
        INCLUDES
            ${CMAKE_CURRENT_SOURCE_DIR}
            ${CMAKE_SOURCE_DIR}/include
            ${CMAKE_BINARY_DIR}/proto
        DEPENDENCIES feuerbird-libos feuerbird-capnp
    )

    set_target_properties(hello-channel-demo PROPERTIES
        OUTPUT_NAME "hello-channel"
        PREFIX ""
    )
endif()

# Typed channel demo (requires unified_chan functions)
# NOTE: Disabled for host builds - requires kernel syscalls (exo_alloc_page)
# that are only available when running on the FeuerBird kernel
# if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/typed_chan_demo.c")
#     feuerbird_add_executable(typed-chan-demo
#         SOURCES typed_chan_demo.c
#         INCLUDES
#             ${CMAKE_CURRENT_SOURCE_DIR}
#             ${CMAKE_SOURCE_DIR}/include
#         DEPENDENCIES feuerbird-libos feuerbird-chan
#     )
#
#     set_target_properties(typed-chan-demo PROPERTIES
#         OUTPUT_NAME "typed-chan-demo"
#         PREFIX ""
#     )
# endif()

# Typed channel send/receive demos (require Cap'n Proto for driver.capnp.h)
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/typed_chan_send.c" AND USE_CAPNP)
    feuerbird_add_executable(typed-chan-send
        SOURCES typed_chan_send.c
        INCLUDES
            ${CMAKE_CURRENT_SOURCE_DIR}
            ${CMAKE_SOURCE_DIR}/include
            ${CMAKE_BINARY_DIR}/proto
        DEPENDENCIES feuerbird-libos feuerbird-chan feuerbird-capnp
    )

    set_target_properties(typed-chan-send PROPERTIES
        OUTPUT_NAME "typed-chan-send"
        PREFIX ""
    )
endif()

if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/typed_chan_recv.c" AND USE_CAPNP)
    feuerbird_add_executable(typed-chan-recv
        SOURCES typed_chan_recv.c
        INCLUDES
            ${CMAKE_CURRENT_SOURCE_DIR}
            ${CMAKE_SOURCE_DIR}/include
            ${CMAKE_BINARY_DIR}/proto
        DEPENDENCIES feuerbird-libos feuerbird-chan feuerbird-capnp
    )

    set_target_properties(typed-chan-recv PROPERTIES
        OUTPUT_NAME "typed-chan-recv"
        PREFIX ""
    )
endif()

# Affine channel demo (requires Cap'n Proto for driver.capnp.h)
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/affine_channel_demo.c" AND USE_CAPNP)
    feuerbird_add_executable(affine-channel-demo
        SOURCES affine_channel_demo.c
        INCLUDES
            ${CMAKE_CURRENT_SOURCE_DIR}
            ${CMAKE_SOURCE_DIR}/include
            ${CMAKE_BINARY_DIR}/proto
        DEPENDENCIES feuerbird-libos feuerbird-capnp
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
    feuerbird_add_executable(beatty-demo
        SOURCES beatty_demo.c
        INCLUDES 
            ${CMAKE_CURRENT_SOURCE_DIR}
            ${CMAKE_SOURCE_DIR}/include
        DEPENDENCIES feuerbird-libos
    )
    
    set_target_properties(beatty-demo PROPERTIES 
        OUTPUT_NAME "beatty-demo"
        PREFIX ""
    )
endif()

# DAG demo
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/dag_demo.c")
    feuerbird_add_executable(dag-demo
        SOURCES dag_demo.c
        INCLUDES 
            ${CMAKE_CURRENT_SOURCE_DIR}
            ${CMAKE_SOURCE_DIR}/include
        DEPENDENCIES feuerbird-libos
    )
    
    set_target_properties(dag-demo PROPERTIES 
        OUTPUT_NAME "dag-demo"
        PREFIX ""
    )
endif()

# Beatty DAG demo (standalone with math library)
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/beatty_dag_demo.c")
    feuerbird_add_executable(beatty-dag-demo
        SOURCES beatty_dag_demo.c
        INCLUDES
            ${CMAKE_CURRENT_SOURCE_DIR}
            ${CMAKE_SOURCE_DIR}/include
    )

    # Link math library for sqrt()
    target_link_libraries(beatty-dag-demo PRIVATE m)

    set_target_properties(beatty-dag-demo PROPERTIES
        OUTPUT_NAME "beatty-dag-demo"
        PREFIX ""
    )
endif()

# Channel Beatty RCRS demo (requires channel and driver libraries)
# NOTE: Disabled for host builds - requires kernel syscalls (exo_alloc_page, swtch)
# that are only available when running on the FeuerBird kernel
# if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/chan_beatty_rcrs_demo.c")
#     feuerbird_add_executable(chan-beatty-rcrs-demo
#         SOURCES chan_beatty_rcrs_demo.c
#         INCLUDES
#             ${CMAKE_CURRENT_SOURCE_DIR}
#             ${CMAKE_SOURCE_DIR}/include
#         DEPENDENCIES feuerbird-libos feuerbird-chan
#     )
#
#     # Link driver library if available
#     if(TARGET feuerbird-libos-driver)
#         target_link_libraries(chan-beatty-rcrs-demo PRIVATE feuerbird-libos-driver)
#     endif()
#
#     set_target_properties(chan-beatty-rcrs-demo PROPERTIES
#         OUTPUT_NAME "chan-beatty-rcrs-demo"
#         PREFIX ""
#     )
# endif()

# Channel DAG supervisor demo (requires Cap'n Proto for driver.capnp.h)
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/chan_dag_supervisor_demo.c" AND USE_CAPNP)
    feuerbird_add_executable(chan-dag-supervisor-demo
        SOURCES chan_dag_supervisor_demo.c
        INCLUDES
            ${CMAKE_CURRENT_SOURCE_DIR}
            ${CMAKE_SOURCE_DIR}/include
            ${CMAKE_BINARY_DIR}/proto
        DEPENDENCIES feuerbird-libos feuerbird-capnp
    )

    set_target_properties(chan-dag-supervisor-demo PROPERTIES
        OUTPUT_NAME "chan-dag-supervisor-demo"
        PREFIX ""
    )
endif()

# ═════════════════════════════════════════════════════════════════════
# HARDWARE AND SYSTEM DEMONSTRATIONS
# ═════════════════════════════════════════════════════════════════════

# Frame buffer device demo (requires DDEKit)
# NOTE: Disabled for host builds - requires kernel syscalls (ddekit_init, etc.)
# that are only available when running on the FeuerBird kernel
# if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/fbdev_demo.c")
#     feuerbird_add_executable(fbdev-demo
#         SOURCES fbdev_demo.c
#         INCLUDES
#             ${CMAKE_CURRENT_SOURCE_DIR}
#             ${CMAKE_SOURCE_DIR}/include
#         DEPENDENCIES feuerbird-libos feuerbird-ddekit
#     )
#
#     set_target_properties(fbdev-demo PROPERTIES
#         OUTPUT_NAME "fbdev-demo"
#         PREFIX ""
#     )
# endif()

# Hypervisor demo
# NOTE: Disabled for host builds - requires kernel syscalls (exo_alloc_hypervisor, etc.)
# that are only available when running on the FeuerBird kernel
# if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/hv_demo.c")
#     feuerbird_add_executable(hv-demo
#         SOURCES hv_demo.c
#         INCLUDES
#             ${CMAKE_CURRENT_SOURCE_DIR}
#             ${CMAKE_SOURCE_DIR}/include
#         DEPENDENCIES feuerbird-libos
#     )
#
#     set_target_properties(hv-demo PROPERTIES
#         OUTPUT_NAME "hv-demo"
#         PREFIX ""
#     )
# endif()

# DDEKit port demo
# NOTE: Disabled for host builds - requires kernel syscalls (ddekit_* functions)
# that are only available when running on the FeuerBird kernel
# if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/ddekit_port_demo.c")
#     feuerbird_add_executable(ddekit-port-demo
#         SOURCES ddekit_port_demo.c
#         INCLUDES
#             ${CMAKE_CURRENT_SOURCE_DIR}
#             ${CMAKE_SOURCE_DIR}/include
#         DEPENDENCIES feuerbird-libos feuerbird-ddekit
#     )
#
#     set_target_properties(ddekit-port-demo PROPERTIES
#         OUTPUT_NAME "ddekit-port-demo"
#         PREFIX ""
#     )
# endif()

# ═════════════════════════════════════════════════════════════════════
# SYNCHRONIZATION DEMONSTRATIONS
# ═════════════════════════════════════════════════════════════════════

# Queue spinlock demo (standalone - no libos dependency)
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/qspin_demo.c")
    feuerbird_add_executable(qspin-demo
        SOURCES qspin_demo.c
        INCLUDES
            ${CMAKE_CURRENT_SOURCE_DIR}
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
# NOTE: Disabled until microkernel library is implemented
# Requires: include/microkernel/microkernel.h and associated library
# if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/microkernel_rcrs_demo.c")
#     feuerbird_add_executable(microkernel-rcrs-demo
#         SOURCES microkernel_rcrs_demo.c
#         INCLUDES
#             ${CMAKE_CURRENT_SOURCE_DIR}
#             ${CMAKE_SOURCE_DIR}/include
#         DEPENDENCIES feuerbird-libos feuerbird-microkernel
#     )
#
#     set_target_properties(microkernel-rcrs-demo PROPERTIES
#         OUTPUT_NAME "microkernel-rcrs-demo"
#         PREFIX ""
#     )
# endif()

# IRQ lambda policy demo
# NOTE: Disabled for host builds - requires kernel syscalls (exo_alloc_irq, irq_wait, irq_ack)
# that are only available when running on the FeuerBird kernel
# if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/irq_lambda_policy.c")
#     feuerbird_add_executable(irq-lambda-policy-demo
#         SOURCES irq_lambda_policy.c
#         INCLUDES
#             ${CMAKE_CURRENT_SOURCE_DIR}
#             ${CMAKE_SOURCE_DIR}/include
#         DEPENDENCIES feuerbird-libos
#     )
#
#     set_target_properties(irq-lambda-policy-demo PROPERTIES
#         OUTPUT_NAME "irq-lambda-policy-demo"
#         PREFIX ""
#     )
# endif()

# ═════════════════════════════════════════════════════════════════════
# POSIX COMPATIBILITY DEMONSTRATIONS
# ═════════════════════════════════════════════════════════════════════

# POSIX LibOS extra test
# NOTE: Disabled for host builds due to system header conflicts
# This test is designed for freestanding builds on the FeuerBird kernel
# The mix of <sys/socket.h> with project headers causes sockaddr_in redefinition
# if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/libos_posix_extra_test.c")
#     feuerbird_add_executable(libos-posix-extra-test
#         SOURCES libos_posix_extra_test.c
#         INCLUDES
#             ${CMAKE_CURRENT_SOURCE_DIR}
#             ${CMAKE_SOURCE_DIR}/include
#         DEPENDENCIES feuerbird-libos
#     )
#
#     set_target_properties(libos-posix-extra-test PROPERTIES
#         OUTPUT_NAME "libos-posix-extra-test"
#         PREFIX ""
#     )
# endif()

# POSIX current working directory test
# Uses hosted libos (host syscalls) so it can run on development host
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/posix_cwd_test.c")
    if(TARGET feuerbird-libos-hosted)
        feuerbird_add_executable(posix-cwd-test
            SOURCES posix_cwd_test.c
            INCLUDES
                ${CMAKE_CURRENT_SOURCE_DIR}
                ${CMAKE_SOURCE_DIR}/include
                ${CMAKE_SOURCE_DIR}/libos
            DEPENDENCIES feuerbird-libos-hosted
        )

        set_target_properties(posix-cwd-test PROPERTIES
            OUTPUT_NAME "posix-cwd-test"
            PREFIX ""
        )
    endif()
endif()

# POSIX miscellaneous test
# NOTE: Disabled for host builds - requires libfs functions (libfs_open, etc.)
# that are only available when running on the FeuerBird kernel
# if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/posix_misc_test.c")
#     feuerbird_add_executable(posix-misc-test
#         SOURCES posix_misc_test.c
#         INCLUDES
#             ${CMAKE_CURRENT_SOURCE_DIR}
#             ${CMAKE_SOURCE_DIR}/include
#         DEPENDENCIES feuerbird-libos
#     )
#
#     set_target_properties(posix-misc-test PROPERTIES
#         OUTPUT_NAME "posix-misc-test"
#         PREFIX ""
#     )
# endif()

# POSIX socket test
# NOTE: Disabled for host builds - requires libfs/kernel functions
# if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/posix_socket_test.c")
#     feuerbird_add_executable(posix-socket-test
#         SOURCES posix_socket_test.c
#         INCLUDES
#             ${CMAKE_CURRENT_SOURCE_DIR}
#             ${CMAKE_SOURCE_DIR}/include
#         DEPENDENCIES feuerbird-libos
#     )
#
#     set_target_properties(posix-socket-test PROPERTIES
#         OUTPUT_NAME "posix-socket-test"
#         PREFIX ""
#     )
# endif()

# ═════════════════════════════════════════════════════════════════════
# STREAMING DEMONSTRATIONS
# ═════════════════════════════════════════════════════════════════════

# ExoStream demo (standalone - no libos dependency)
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/exo_stream_demo.c")
    feuerbird_add_executable(exo-stream-demo
        SOURCES exo_stream_demo.c
        INCLUDES
            ${CMAKE_CURRENT_SOURCE_DIR}
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
if(TARGET feuerbird-msgqueue-demo)
    add_custom_target(run-msgqueue-demo
        COMMAND feuerbird-msgqueue-demo
        DEPENDS feuerbird-msgqueue-demo
        COMMENT "Running message queue demonstration"
    )
endif()

if(TARGET feuerbird-wumpus-game)
    add_custom_target(run-wumpus
        COMMAND feuerbird-wumpus-game
        DEPENDS feuerbird-wumpus-game
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
    if(target MATCHES "^feuerbird-.*-demo$" OR target MATCHES "^feuerbird-.*-test$" OR target STREQUAL "feuerbird-wumpus-game")
        list(APPEND DEMO_TARGETS ${target})
    endif()
endforeach()

set(FEUERBIRD_EXOKERNEL_DEMO_TARGETS ${DEMO_TARGETS} PARENT_SCOPE)

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
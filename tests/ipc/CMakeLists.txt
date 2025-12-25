# IPC Test Suite
# Tests advanced IPC capabilities and mathematical optimization

# Stress test IPC
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/stress_test_ipc.c")
    phoenix_add_executable(stress-test-ipc
        SOURCES stress_test_ipc.c
        INCLUDES 
            ${CMAKE_CURRENT_SOURCE_DIR}
            ${CMAKE_SOURCE_DIR}/include
        DEPENDENCIES phoenix-libos
    )
    
    target_link_libraries(stress-test-ipc PRIVATE m)
    target_compile_features(stress-test-ipc PRIVATE c_std_17)
    
    set_target_properties(stress-test-ipc PROPERTIES 
        OUTPUT_NAME "stress-test-ipc"
        PREFIX ""
    )
    
    # Add as CTest
    add_test(NAME IPCStressTest 
             COMMAND stress-test-ipc)
endif()

# Custom target for running IPC tests
add_custom_target(run-ipc-tests
    COMMENT "Running IPC test suite"
)

if(TARGET stress-test-ipc)
    add_custom_target(run-stress-test-ipc
        COMMAND stress-test-ipc
        DEPENDS stress-test-ipc
        COMMENT "Running IPC stress test"
    )
    add_dependencies(run-ipc-tests run-stress-test-ipc)
endif()

message(STATUS "IPC tests configured:")
message(STATUS "  - IPC stress test: ✓")
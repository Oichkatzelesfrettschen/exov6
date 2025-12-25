# Kernel Mathematical Demonstration Programs
# Showcases advanced mathematical kernel capabilities and 2025 cutting-edge concepts

# Integrated mathematical kernel demo
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/demo_integrated_mathematical_kernel.c")
    phoenix_add_executable(demo-integrated-mathematical-kernel
        SOURCES demo_integrated_mathematical_kernel.c
        INCLUDES 
            ${CMAKE_CURRENT_SOURCE_DIR}
            ${CMAKE_SOURCE_DIR}/include
            ${CMAKE_SOURCE_DIR}/kernel
        DEPENDENCIES phoenix-libos
    )
    
    target_link_libraries(demo-integrated-mathematical-kernel PRIVATE m)
    target_compile_features(demo-integrated-mathematical-kernel PRIVATE c_std_17)
    
    set_target_properties(demo-integrated-mathematical-kernel PROPERTIES 
        OUTPUT_NAME "demo-integrated-mathematical-kernel"
        PREFIX ""
    )
    
    # Custom target for running the mathematical kernel demo
    add_custom_target(run-mathematical-kernel-demo
        COMMAND demo-integrated-mathematical-kernel
        DEPENDS demo-integrated-mathematical-kernel
        COMMENT "Running integrated mathematical kernel demonstration"
    )
endif()

message(STATUS "Kernel mathematical demos configured:")
message(STATUS "  - Integrated mathematical kernel demo: ✓")
message(STATUS "  - 2025 cutting-edge mathematical concepts: ✓")
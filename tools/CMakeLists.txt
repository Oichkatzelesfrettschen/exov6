# tools/CMakeLists.txt - Development Tools and Utilities

# ═════════════════════════════════════════════════════════════════════
# ANALYSIS AND METRICS TOOLS
# ═════════════════════════════════════════════════════════════════════

# FeuerBird metrics tool
# NOTE: Host tools should NOT include ${CMAKE_SOURCE_DIR}/include as it contains
# freestanding kernel headers that shadow system headers (sys/stat.h, etc.)
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/feuerbird_metrics.c")
    add_executable(feuerbird-metrics feuerbird_metrics.c)
    target_include_directories(feuerbird-metrics PRIVATE ${CMAKE_CURRENT_SOURCE_DIR})
    target_compile_definitions(feuerbird-metrics PRIVATE FEUERBIRD_METRICS_MAIN)

    set_target_properties(feuerbird-metrics PROPERTIES
        OUTPUT_NAME "feuerbird-metrics"
        PREFIX ""
    )

    # Create feuerbird_prof alias for backward compatibility
    add_executable(feuerbird_prof ALIAS feuerbird-metrics)
endif()

# Compiler utilities
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/compiler_utils.c")
    # Host tool - use standard library and minimal includes
    add_library(feuerbird-compiler-utils STATIC compiler_utils.c)
    target_include_directories(feuerbird-compiler-utils PRIVATE ${CMAKE_CURRENT_SOURCE_DIR})
endif()

# ═════════════════════════════════════════════════════════════════════
# CODE ANALYSIS TOOLS
# ═════════════════════════════════════════════════════════════════════

# Header graph analyzer (Python script - create wrapper if needed)
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/header_graph.py")
    # Find Python interpreter
    find_package(Python3 COMPONENTS Interpreter)
    
    if(Python3_FOUND)
        # Create a wrapper script or install target
        configure_file(
            "${CMAKE_CURRENT_SOURCE_DIR}/header_graph.py"
            "${CMAKE_BINARY_DIR}/bin/header-graph"
            COPYONLY
        )
        
        # Make it executable
        if(UNIX)
            file(CHMOD "${CMAKE_BINARY_DIR}/bin/header-graph" 
                PERMISSIONS OWNER_READ OWNER_WRITE OWNER_EXECUTE 
                           GROUP_READ GROUP_EXECUTE 
                           WORLD_READ WORLD_EXECUTE
            )
        endif()
    endif()
endif()

# File organizer (Python script)
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/file_organizer.py")
    find_package(Python3 COMPONENTS Interpreter)
    
    if(Python3_FOUND)
        configure_file(
            "${CMAKE_CURRENT_SOURCE_DIR}/file_organizer.py"
            "${CMAKE_BINARY_DIR}/bin/file-organizer"
            COPYONLY
        )
        
        if(UNIX)
            file(CHMOD "${CMAKE_BINARY_DIR}/bin/file-organizer" 
                PERMISSIONS OWNER_READ OWNER_WRITE OWNER_EXECUTE 
                           GROUP_READ GROUP_EXECUTE 
                           WORLD_READ WORLD_EXECUTE
            )
        endif()
    endif()
endif()

# GDB utilities (Python script)
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/gdbutil.py")
    find_package(Python3 COMPONENTS Interpreter)
    
    if(Python3_FOUND)
        configure_file(
            "${CMAKE_CURRENT_SOURCE_DIR}/gdbutil.py"
            "${CMAKE_BINARY_DIR}/bin/gdbutil"
            COPYONLY
        )
        
        if(UNIX)
            file(CHMOD "${CMAKE_BINARY_DIR}/bin/gdbutil" 
                PERMISSIONS OWNER_READ OWNER_WRITE OWNER_EXECUTE 
                           GROUP_READ GROUP_EXECUTE 
                           WORLD_READ WORLD_EXECUTE
            )
        endif()
    endif()
endif()

# ═════════════════════════════════════════════════════════════════════
# BUILD TOOLS
# ═════════════════════════════════════════════════════════════════════

# Network Compiler Compiler (if needed)
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/ncc.c")
    add_executable(ncc ncc.c)
    target_include_directories(ncc PRIVATE ${CMAKE_CURRENT_SOURCE_DIR})
    target_link_libraries(ncc PRIVATE feuerbird-compiler-utils)
    
    set_target_properties(ncc PROPERTIES 
        OUTPUT_NAME "ncc"
        PREFIX ""
    )
endif()

# ═════════════════════════════════════════════════════════════════════
# JAVASCRIPT TOOLS
# ═════════════════════════════════════════════════════════════════════

# File counter (Node.js script)
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/file_count.js")
    find_program(NODE_EXECUTABLE NAMES node nodejs)
    
    if(NODE_EXECUTABLE)
        configure_file(
            "${CMAKE_CURRENT_SOURCE_DIR}/file_count.js"
            "${CMAKE_BINARY_DIR}/bin/file-count.js"
            COPYONLY
        )
        
        # Create wrapper script
        if(UNIX)
            file(WRITE "${CMAKE_BINARY_DIR}/bin/file-count" 
                "#!/bin/bash\n${NODE_EXECUTABLE} \"${CMAKE_BINARY_DIR}/bin/file-count.js\" \"$@\"\n"
            )
            file(CHMOD "${CMAKE_BINARY_DIR}/bin/file-count" 
                PERMISSIONS OWNER_READ OWNER_WRITE OWNER_EXECUTE 
                           GROUP_READ GROUP_EXECUTE 
                           WORLD_READ WORLD_EXECUTE
            )
        endif()
    endif()
endif()

# ═════════════════════════════════════════════════════════════════════
# CUSTOM TARGETS FOR TOOL OPERATIONS
# ═════════════════════════════════════════════════════════════════════

# Header dependency analysis target
if(Python3_FOUND AND EXISTS "${CMAKE_BINARY_DIR}/bin/header-graph")
    add_custom_target(analyze-headers
        COMMAND "${CMAKE_BINARY_DIR}/bin/header-graph" "${CMAKE_SOURCE_DIR}"
        WORKING_DIRECTORY "${CMAKE_SOURCE_DIR}"
        COMMENT "Analyzing header dependencies"
    )
endif()

# File organization target
if(Python3_FOUND AND EXISTS "${CMAKE_BINARY_DIR}/bin/file-organizer")
    add_custom_target(organize-files
        COMMAND "${CMAKE_BINARY_DIR}/bin/file-organizer" "${CMAKE_SOURCE_DIR}"
        WORKING_DIRECTORY "${CMAKE_SOURCE_DIR}"
        COMMENT "Organizing project files"
    )
endif()

# Code metrics target
if(TARGET feuerbird-metrics)
    add_custom_target(code-metrics
        COMMAND feuerbird-metrics "${CMAKE_SOURCE_DIR}"
        DEPENDS feuerbird-metrics
        WORKING_DIRECTORY "${CMAKE_SOURCE_DIR}"
        COMMENT "Generating code metrics"
    )
endif()

# File count target
if(NODE_EXECUTABLE AND EXISTS "${CMAKE_BINARY_DIR}/bin/file-count")
    add_custom_target(count-files
        COMMAND "${CMAKE_BINARY_DIR}/bin/file-count" "${CMAKE_SOURCE_DIR}"
        WORKING_DIRECTORY "${CMAKE_SOURCE_DIR}"
        COMMENT "Counting project files"
    )
endif()

# ═════════════════════════════════════════════════════════════════════
# TOOL INSTALLATION
# ═════════════════════════════════════════════════════════════════════

# Install C++ tools
if(TARGET feuerbird-metrics)
    install(TARGETS feuerbird-metrics
        RUNTIME DESTINATION bin
        COMPONENT tools
    )
endif()

if(TARGET feuerbird-compiler-utils)
    install(TARGETS feuerbird-compiler-utils
        RUNTIME DESTINATION bin
        COMPONENT tools
    )
endif()

if(TARGET feuerbird-ncc)
    install(TARGETS feuerbird-ncc
        RUNTIME DESTINATION bin
        COMPONENT tools
    )
endif()

# Install script tools
if(EXISTS "${CMAKE_BINARY_DIR}/bin/header-graph")
    install(PROGRAMS "${CMAKE_BINARY_DIR}/bin/header-graph"
        DESTINATION bin
        COMPONENT tools
    )
endif()

if(EXISTS "${CMAKE_BINARY_DIR}/bin/file-organizer")
    install(PROGRAMS "${CMAKE_BINARY_DIR}/bin/file-organizer"
        DESTINATION bin
        COMPONENT tools
    )
endif()

if(EXISTS "${CMAKE_BINARY_DIR}/bin/gdbutil")
    install(PROGRAMS "${CMAKE_BINARY_DIR}/bin/gdbutil"
        DESTINATION bin
        COMPONENT tools
    )
endif()

if(EXISTS "${CMAKE_BINARY_DIR}/bin/file-count")
    install(PROGRAMS "${CMAKE_BINARY_DIR}/bin/file-count"
        DESTINATION bin
        COMPONENT tools
    )
endif()

# ═════════════════════════════════════════════════════════════════════
# EXPORTS
# ═════════════════════════════════════════════════════════════════════

set(FEUERBIRD_EXOKERNEL_TOOL_TARGETS
    PARENT_SCOPE
)

# Collect tool targets
set(TOOL_TARGETS)
if(TARGET feuerbird-metrics)
    list(APPEND TOOL_TARGETS feuerbird-metrics)
endif()
if(TARGET feuerbird-compiler-utils)
    list(APPEND TOOL_TARGETS feuerbird-compiler-utils)
endif()
if(TARGET feuerbird-ncc)
    list(APPEND TOOL_TARGETS feuerbird-ncc)
endif()

if(TOOL_TARGETS)
    set(FEUERBIRD_EXOKERNEL_TOOL_TARGETS ${TOOL_TARGETS} PARENT_SCOPE)
endif()

message(STATUS "Tools zone configured:")
if(TARGET feuerbird-metrics)
    message(STATUS "  - FeuerBird metrics: [OK]")
endif()
if(TARGET feuerbird-compiler-utils)
    message(STATUS "  - Compiler utilities: ✓")
endif()
if(TARGET feuerbird-ncc)
    message(STATUS "  - Network compiler: ✓")
endif()
if(Python3_FOUND)
    message(STATUS "  - Python analysis tools: ✓")
endif()
if(NODE_EXECUTABLE)
    message(STATUS "  - JavaScript tools: ✓")
endif()
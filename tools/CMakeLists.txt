# tools/CMakeLists.txt - Development Tools and Utilities

# ═════════════════════════════════════════════════════════════════════
# ANALYSIS AND METRICS TOOLS
# ═════════════════════════════════════════════════════════════════════

# Phoenix metrics tool - Host tool, no kernel headers
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/phoenix_metrics.c")
    add_executable(phoenix-metrics phoenix_metrics.c)
    target_include_directories(phoenix-metrics PRIVATE ${CMAKE_CURRENT_SOURCE_DIR})
    target_compile_definitions(phoenix-metrics PRIVATE PHOENIX_METRICS_MAIN)
    target_compile_options(phoenix-metrics PRIVATE -Wall -Wextra)
    
    set_target_properties(phoenix-metrics PROPERTIES 
        OUTPUT_NAME "phoenix-metrics"
        PREFIX ""
    )
    
    # Create phoenix_prof alias for backward compatibility
    add_executable(phoenix_prof ALIAS phoenix-metrics)
endif()

# Compiler utilities
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/compiler_utils.c")
    # Host tool - use standard library and minimal includes
    add_library(phoenix-compiler-utils STATIC compiler_utils.c)
    target_include_directories(phoenix-compiler-utils PRIVATE ${CMAKE_CURRENT_SOURCE_DIR})
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
    target_link_libraries(ncc PRIVATE phoenix-compiler-utils)
    
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
if(TARGET phoenix-metrics)
    add_custom_target(code-metrics
        COMMAND phoenix-metrics "${CMAKE_SOURCE_DIR}"
        DEPENDS phoenix-metrics
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
if(TARGET phoenix-metrics)
    install(TARGETS phoenix-metrics
        RUNTIME DESTINATION bin
        COMPONENT tools
    )
endif()

if(TARGET phoenix-compiler-utils)
    install(TARGETS phoenix-compiler-utils
        RUNTIME DESTINATION bin
        COMPONENT tools
    )
endif()

if(TARGET phoenix-ncc)
    install(TARGETS phoenix-ncc
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

set(EXOV6_TOOL_TARGETS
    PARENT_SCOPE
)

# Collect tool targets
set(TOOL_TARGETS)
if(TARGET phoenix-metrics)
    list(APPEND TOOL_TARGETS phoenix-metrics)
endif()
if(TARGET phoenix-compiler-utils)
    list(APPEND TOOL_TARGETS phoenix-compiler-utils)
endif()
if(TARGET phoenix-ncc)
    list(APPEND TOOL_TARGETS phoenix-ncc)
endif()

if(TOOL_TARGETS)
    set(EXOV6_TOOL_TARGETS ${TOOL_TARGETS} PARENT_SCOPE)
endif()

message(STATUS "Tools zone configured:")
if(TARGET phoenix-metrics)
    message(STATUS "  - Phoenix metrics: ✓")
endif()
if(TARGET phoenix-compiler-utils)
    message(STATUS "  - Compiler utilities: ✓")
endif()
if(TARGET phoenix-ncc)
    message(STATUS "  - Network compiler: ✓")
endif()
if(Python3_FOUND)
    message(STATUS "  - Python analysis tools: ✓")
endif()
if(NODE_EXECUTABLE)
    message(STATUS "  - JavaScript tools: ✓")
endif()
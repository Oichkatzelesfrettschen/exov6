# proto/CMakeLists.txt - Protocols and Interface Definitions

# ═════════════════════════════════════════════════════════════════════
# BISON PARSER GENERATION
# ═════════════════════════════════════════════════════════════════════

find_package(BISON)
if(BISON_FOUND AND EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/example.y")
    BISON_TARGET(example_parser
        example.y
        ${CMAKE_CURRENT_BINARY_DIR}/example_parser.c
        DEFINES_FILE ${CMAKE_CURRENT_BINARY_DIR}/example_parser.h
    )
    
    # Create parser library
    exov6_add_library(exov6-example-parser
        STATIC
        SOURCES ${BISON_example_parser_OUTPUTS}
        INCLUDES 
            ${CMAKE_CURRENT_BINARY_DIR}
            ${CMAKE_CURRENT_SOURCE_DIR}
    )
    
    add_custom_target(example_bison DEPENDS ${BISON_example_parser_OUTPUTS})
    add_dependencies(exov6-example-parser example_bison)
endif()

# ═════════════════════════════════════════════════════════════════════
# CAP'N PROTO SUPPORT
# ═════════════════════════════════════════════════════════════════════

if(USE_CAPNP)
    # Find mock capnp compiler
    find_program(MOCK_CAPNPC 
        NAMES mock_capnpc.sh
        PATHS ${CMAKE_SOURCE_DIR}/scripts
        REQUIRED
    )
    
    set(CAPNP_SOURCES)
    set(CAPNP_HEADERS)
    
    # Process driver.capnp
    if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/driver.capnp")
        add_custom_command(
            OUTPUT 
                ${CMAKE_CURRENT_BINARY_DIR}/driver.capnp.c 
                ${CMAKE_CURRENT_BINARY_DIR}/driver.capnp.h
            COMMAND ${MOCK_CAPNPC} ${CMAKE_CURRENT_SOURCE_DIR}/driver.capnp
            DEPENDS ${CMAKE_CURRENT_SOURCE_DIR}/driver.capnp
            WORKING_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}
            COMMENT "Generating Cap'n Proto driver bindings"
        )
        list(APPEND CAPNP_SOURCES ${CMAKE_CURRENT_BINARY_DIR}/driver.capnp.c)
        list(APPEND CAPNP_HEADERS ${CMAKE_CURRENT_BINARY_DIR}/driver.capnp.h)
    endif()
    
    # Process hello.capnp
    if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/hello.capnp")
        add_custom_command(
            OUTPUT 
                ${CMAKE_CURRENT_BINARY_DIR}/hello.capnp.c 
                ${CMAKE_CURRENT_BINARY_DIR}/hello.capnp.h
            COMMAND ${MOCK_CAPNPC} ${CMAKE_CURRENT_SOURCE_DIR}/hello.capnp
            DEPENDS ${CMAKE_CURRENT_SOURCE_DIR}/hello.capnp
            WORKING_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}
            COMMENT "Generating Cap'n Proto hello bindings"
        )
        list(APPEND CAPNP_SOURCES ${CMAKE_CURRENT_BINARY_DIR}/hello.capnp.c)
        list(APPEND CAPNP_HEADERS ${CMAKE_CURRENT_BINARY_DIR}/hello.capnp.h)
    endif()
    
    # Find Cap'n Proto helper sources
    if(EXISTS "${CMAKE_SOURCE_DIR}/libos/capnp/capnp_helpers.c")
        list(APPEND CAPNP_SOURCES ${CMAKE_SOURCE_DIR}/libos/capnp/capnp_helpers.c)
    endif()
    
    if(CAPNP_SOURCES)
        # Create Cap'n Proto library
        exov6_add_library(exov6-capnp
            STATIC
            SOURCES ${CAPNP_SOURCES}
            INCLUDES 
                ${CMAKE_CURRENT_SOURCE_DIR}
                ${CMAKE_CURRENT_BINARY_DIR}
                ${CMAKE_SOURCE_DIR}/libos/capnp
                ${CMAKE_SOURCE_DIR}/include
        )
        
        # Create custom target for generated files
        add_custom_target(capnp_generated DEPENDS ${CAPNP_HEADERS})
        add_dependencies(exov6-capnp capnp_generated)
        
        # Legacy alias
        add_library(capnp ALIAS exov6-capnp)
    endif()
endif()

# ═════════════════════════════════════════════════════════════════════
# PROTOCOL INTERFACE LIBRARY
# ═════════════════════════════════════════════════════════════════════

# Create interface library for protocol headers
exov6_add_library(exov6-protocols
    INTERFACE
    INCLUDES 
        ${CMAKE_CURRENT_SOURCE_DIR}
        ${CMAKE_CURRENT_BINARY_DIR}
        ${CMAKE_SOURCE_DIR}/include
)

# Add dependencies to protocol implementations
set(PROTOCOL_DEPS)
if(TARGET exov6-example-parser)
    list(APPEND PROTOCOL_DEPS exov6-example-parser)
endif()
if(TARGET exov6-capnp)
    list(APPEND PROTOCOL_DEPS exov6-capnp)
endif()

if(PROTOCOL_DEPS)
    target_link_libraries(exov6-protocols INTERFACE ${PROTOCOL_DEPS})
endif()

# ═════════════════════════════════════════════════════════════════════
# EXPORTS
# ═════════════════════════════════════════════════════════════════════

set(EXOV6_PROTOCOL_TARGETS
    exov6-protocols
    PARENT_SCOPE
)

if(TARGET exov6-capnp)
    set(EXOV6_CAPNP_TARGET exov6-capnp PARENT_SCOPE)
endif()

message(STATUS "Protocols zone configured:")
if(BISON_FOUND AND TARGET exov6-example-parser)
    message(STATUS "  - Bison parser: ✓")
endif()
if(USE_CAPNP AND TARGET exov6-capnp)
    message(STATUS "  - Cap'n Proto: ✓")
else()
    message(STATUS "  - Cap'n Proto: Disabled")
endif()
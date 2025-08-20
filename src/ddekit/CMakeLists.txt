# src/ddekit/CMakeLists.txt - Device Driver Environment Kit

# Collect DDEKit sources
file(GLOB DDEKIT_SOURCES *.c)
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/badgerferret")
    file(GLOB BADGERFERRET_SOURCES badgerferret/*.c)
    list(APPEND DDEKIT_SOURCES ${BADGERFERRET_SOURCES})
endif()

# Create DDEKit library using ExoV6 framework
exov6_add_library(exov6-ddekit
    STATIC
    SOURCES ${DDEKIT_SOURCES}
    INCLUDES 
        ${CMAKE_CURRENT_SOURCE_DIR}
        ${CMAKE_SOURCE_DIR}/include
    DEPENDENCIES exov6-architecture
)

# Legacy alias for backward compatibility
add_library(ddekit ALIAS exov6-ddekit)

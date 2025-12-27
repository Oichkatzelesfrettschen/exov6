# src/ddekit/CMakeLists.txt - Device Driver Environment Kit

# Collect DDEKit sources
file(GLOB DDEKIT_SOURCES *.c)
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/badgerferret")
    file(GLOB BADGERFERRET_SOURCES badgerferret/*.c)
    list(APPEND DDEKIT_SOURCES ${BADGERFERRET_SOURCES})
endif()

# Create DDEKit library using FeuerBird Exokernel framework
feuerbird_add_library(feuerbird-ddekit
    STATIC
    SOURCES ${DDEKIT_SOURCES}
    INCLUDES 
        ${CMAKE_CURRENT_SOURCE_DIR}
        ${CMAKE_SOURCE_DIR}/include
    DEPENDENCIES feuerbird-architecture
)

# Legacy alias for backward compatibility
add_library(ddekit ALIAS feuerbird-ddekit)
